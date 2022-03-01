#pragma once

/*
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <divine/cc/filetype.hpp>
#include <llvm/Support/Errc.h>

DIVINE_RELAX_WARNINGS
// #include <clang/Tooling/Tooling.h> // ClangTool
#include <llvm/Support/Path.h>
#include <llvm/Support/VirtualFileSystem.h>
DIVINE_UNRELAX_WARNINGS

#include <brick-fs>
#include <brick-query>
#include <iostream>

namespace divine::cc
{
    enum class VFSError
    {
        InvalidIncludePath = 1000 // avoid clash with LLVM's error codes, they don't check category
    };

    struct VFSErrorCategory : std::error_category
    {
        const char *name() const noexcept override { return "DIVINE VFS error"; }

        std::string message( int condition ) const override
        {
            switch ( VFSError( condition ) )
            {
                case VFSError::InvalidIncludePath:
                    return "Invalid include path, not accessible in DIVINE";
            }

            return "Unknown VFSError";
        }
    };

    static std::error_code make_error_code( VFSError derr )
    {
        return std::error_code( int( derr ), VFSErrorCategory() );
    }

} // divine::cc


namespace std
{
    template<>
    struct is_error_code_enum< divine::cc::VFSError > : std::true_type { };
}


namespace divine::cc
{
    // A virtual filesystem implementing the Clang's interface, used, for example,
    // to allow compiler provided header files without the need to store them
    // explicitly on the physical filesystem
    struct VFS : llvm::vfs::FileSystem
    {

        // The result of a 'status' operation
        using Status = llvm::vfs::Status;

      private:

        // adapt file map to the expectations of LLVM's VFS
        struct File : llvm::vfs::File
        {
            File( llvm::StringRef content, Status stat ) :
                content( content ), stat( stat )
            { }

            llvm::ErrorOr< Status > status() override { return stat; }

            auto getBuffer( const llvm::Twine &/* path */, int64_t /* fileSize */ = -1,
                            bool /* requiresNullTerminator */ = true,
                            bool /* IsVolatile */ = false ) ->
                llvm::ErrorOr< std::unique_ptr< llvm::MemoryBuffer > > override
            {
                return { llvm::MemoryBuffer::getMemBuffer( content ) };
            }

            std::error_code close() override { return std::error_code(); }

          private:
            llvm::StringRef content;
            Status stat;
        };

        std::error_code setCurrentWorkingDirectory( const llvm::Twine &path ) override
        {
            auto oldpwd = _cwd;
            _cwd = brq::is_absolute( path.str() ) ? path.str() : brq::join_path( _cwd, path.str() );
            ASSERT_EQ( oldpwd, _cwd );
            return std::error_code();
        }

        llvm::ErrorOr< std::string > getCurrentWorkingDirectory() const override
        {
            return _cwd;
        }

        static auto doesNotExist() // forward to the real FS
        {
            return std::error_code( llvm::errc::no_such_file_or_directory );
        }

        static auto blockAccess( const llvm::Twine & )
        {
            return std::error_code( VFSError::InvalidIncludePath );
        }

        Status statpath( const std::string &path, llvm::vfs::Status stat )
        {
            return Status::copyWithNewName( stat, path );
        }

      public:

        VFS() : _cwd( brq::getcwd() ) {}

        std::string normal( std::string p )
        {
            return brq::normalize_path( p );
        }

        auto status( const llvm::Twine &_path ) ->
            llvm::ErrorOr< llvm::vfs::Status > override
        {
            auto path = normal( _path.str() );
            auto it = filemap.find( path );
            if ( it != filemap.end() )
                return statpath( path, it->second.second );
            else if ( allowed( path ) )
                return { doesNotExist() };
            return { blockAccess( path ) };
        }

        auto openFileForRead( const llvm::Twine &_path ) ->
            llvm::ErrorOr< std::unique_ptr< llvm::vfs::File > > override
        {
            auto path = normal( _path.str() );

            auto it = filemap.find( path );
            if ( it != filemap.end() )
                return mkfile( it, statpath( path, it->second.second ) );
            else if ( allowed( path ) )
                return { doesNotExist() };
            return { blockAccess( path ) };
        }

        auto dir_begin( const llvm::Twine &_path, std::error_code & ) ->
            llvm::vfs::directory_iterator override
        {
            std::cerr << "DVFS:dir_begin " << normal( _path.str() ) << std::endl;
            NOT_IMPLEMENTED();
        }

        void allowPath( std::string path )
        {
            path = normal( path );
            allowedPrefixes.insert( path );
            auto parts = brq::split_path( path );
            addDir( parts.begin(), parts.end() );
        }

        void addFile( std::string name, std::string contents, bool allowOverride = false )
        {
            storage.emplace_back( std::move( contents ) );
            addFile( name, llvm::StringRef( storage.back() ), allowOverride );
        }

        void addFile( std::string path, llvm::StringRef contents, bool allowOverride = false )
        {
            ASSERT( allowOverride || !filemap.count( path ) );
            auto &ref = filemap[ path ];
            ref.first = contents;
            auto name = llvm::sys::path::filename( path );
            ref.second = llvm::vfs::Status( name,
                            llvm::vfs::getNextVirtualUniqueID(),
                            llvm::sys::TimePoint<>(), 0, 0, contents.size(),
                            llvm::sys::fs::file_type::regular_file,
                            llvm::sys::fs::perms::all_all );
            auto parts = brq::split_path( path );
            if ( !parts.empty() )
                addDir( parts.begin(), parts.end() - 1 );
        }

        template< typename It >
        void addDir( It begin, It end )
        {
            for ( auto it = begin; it < end; ++it )
            {
                auto path = brq::join_path( begin, std::next( it ) );
                filemap[ path ] = { "", llvm::vfs::Status( *it,
                        llvm::vfs::getNextVirtualUniqueID(),
                        llvm::sys::TimePoint<>(), 0, 0, 0,
                        llvm::sys::fs::file_type::directory_file,
                        llvm::sys::fs::perms::all_all ) };
            }
        }

        std::vector< std::string > filesMappedUnder( std::string path )
        {
            auto prefix = brq::split_path( path );
            auto is_prefix = [&]( auto p )
            {
                auto split = brq::split_path( p );
                return split.size() >= prefix.size()
                       && std::equal( prefix.begin(), prefix.end(), split.begin() );
            };

            return brick::query::query( filemap )
                .filter( []( auto &pair ) { return !pair.second.second.isDirectory(); } )
                .map( []( auto &pair ) { return pair.first; } )
                .filter( is_prefix )
                .freeze();
        }

      private:

        bool allowed( std::string path )
        {
            if ( path.empty() || brq::is_relative( path ) )
                return true; // relative or .

            auto parts = brq::split_path( path );
            for ( auto it = std::next( parts.begin() ); it < parts.end(); ++it )
                if ( allowedPrefixes.count( brq::join_path( parts.begin(), it ) ) )
                    return true;
            return false;
        }

        template< typename It >
        std::unique_ptr< llvm::vfs::File > mkfile( It it, llvm::vfs::Status stat )
        {
            return std::make_unique< File >( it->second.first, stat );
        }

        std::map< std::string, std::pair< llvm::StringRef, llvm::vfs::Status > > filemap;
        std::vector< std::string > storage;
        std::set< std::string > allowedPrefixes;
        std::string _cwd;
    };
} // divine::cc

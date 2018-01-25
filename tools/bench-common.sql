-- Tested with PostgreSQL and SQLite3.

-- hardware specs
create table cpu( id   serial primary key not null,
                  model varchar unique not null );

create table pool( id   serial primary key not null,
                   name varchar unique not null );

create table machine(id    serial primary key not null,
                     cpu   integer references cpu(id) not null,
                     cores integer not null,
                     mem   integer not null,
                     unique ( cpu, cores, mem ) );

-- model checker inputs
create table source( id   serial  primary key not null,
                     sha  char(64) not null unique,
                     text blob     not null );

create table model( id       serial primary key not null,
                    name     varchar not null,
                    variant  varchar,
                    revision integer not null,
                    script   integer references source( id ) not null,
                    unique( name, variant, revision ) );

create table model_srcs( model    integer references model( id ) not null,
                         source   integer references source( id ) not null,
                         filename varchar not null,
                         unique ( model, filename ) );

create table tag( id serial primary key not null,
                  name varchar unique not null );

create table model_tags( model integer references model( id ) not null,
                         tag integer references tag( id ) not null,
                         unique ( model, tag ) );

-- model checker versions
create table build( id          serial primary key not null,
                    version     varchar  not null,
                    source_sha  char(40) not null,
                    runtime_sha char(40) not null,
                    build_type  varchar  not null,
                    is_release  boolean  not null,
                    unique( version, source_sha, runtime_sha, build_type ) );

-- ties the machine and the model checker version together
create table instance( id      serial primary key not null,
                       build   integer references build( id ) not null,
                       machine integer references machine( id ) not null,
                       unique( build, machine ) );

create table execution( id       serial primary key not null,
                        instance integer references instance( id ) not null,
                        started  timestamp default current_timestamp not null,
                        time_lart   integer, -- milliseconds
                        time_load   integer, -- milliseconds
                        time_boot   integer, -- milliseconds
                        time_search integer, -- milliseconds
                        time_smt    integer, -- milliseconds
                        time_ce     integer, -- milliseconds
                        states      integer,
                        result   char(1) default 'U' not null ); -- V = valid, E = error, B = boot error, U = unknown

create table pool_log( id serial primary key,
                       seq integer not null,
                       stamp timestamp default current_timestamp not null,
                       execution integer references execution( id ) not null,
                       pool integer references pool( id ) not null,
                       items integer not null,
                       used integer not null,
                       held integer not null );

create table search_log( id serial primary key,
                         seq integer not null,
                         stamp timestamp default current_timestamp not null,
                         execution integer references execution( id ) not null,
                         states integer not null,
                         queued integer not null );

-- benchmarking job: model + instance → execution
create table job( id        serial primary key not null,
                  model     integer references model( id ) not null,
                  instance  integer references instance( id ) not null,
                  execution integer references execution( id ),
                  status    char(1) not null ); -- P = pending, R = running, D = done

-- attach notes to a particular build
create table build_notes( id serial primary key,
                          build integer references build( id ),
                          note varchar );

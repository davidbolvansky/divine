#pragma once

#include <vector>
#include <memory>
#include <string>

namespace divine {
namespace ui {

struct Interface : std::enable_shared_from_this< Interface >
{
    virtual std::shared_ptr< Interface > resolve()
    {
        return shared_from_this();
    }

    virtual int main() = 0;
    virtual void signal( int ) {}
    virtual void exception( std::exception & ) {}
    virtual ~Interface() {}
};


}
}

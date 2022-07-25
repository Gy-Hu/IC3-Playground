//
// Created by galls2 on 30/09/19.
//

#include "aig_to_aag.h"

/***************************************************************************
Copyright (c) 2006-2007, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***************************************************************************/

#include "aiger.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdarg.h>
#include <utils/omg_exception.h>

typedef struct stream stream;
typedef struct memory memory;

struct stream
{
    double bytes;
    FILE *file;
};

struct memory
{
    double bytes;
    double max;
};

static void *
aigtoaig_malloc (memory * m, size_t bytes)
{
    m->bytes += bytes;
    assert (m->bytes);
    if (m->bytes > m->max)
        m->max = m->bytes;
    return malloc (bytes);
}

static void
aigtoaig_free (memory * m, void *ptr, size_t bytes)
{
    assert (m->bytes >= bytes);
    m->bytes -= bytes;
    free (ptr);
}

struct StringWriter
{
    StringWriter() = default;
    std::string current_line;
    std::vector<std::string> lines;
    void write_char(char ch)
    {
        if (ch == '\n')
        {
            lines.push_back(current_line);
            current_line.clear();
        }
        else
        {
            current_line += ch;
        }
    }
};

int string_writer_put(char to_write, StringWriter* write_to)
{
    write_to->write_char(to_write);
    return (int) to_write;
}

std::vector<std::string> aig_to_aag_lines(const std::string& aig_path) {

    const char *src = aig_path.data(), *error;
    memory memory;
    aiger *aiger;


    memory.max = memory.bytes = 0;
    aiger = aiger_init_mem(&memory,
                           (aiger_malloc) aigtoaig_malloc,
                           (aiger_free) aigtoaig_free);

    error = aiger_open_and_read_from_file(aiger, src);
    if (error) {
        throw OmgException(std::string("Aig Read error: ").append(error).data());
    }


    StringWriter string_writer;

    if (!aiger_write_generic(aiger, aiger_ascii_mode,
                             &string_writer, (aiger_put) string_writer_put))
        throw OmgException("Aig Write error!");


    aiger_reset(aiger);


    return string_writer.lines;
}




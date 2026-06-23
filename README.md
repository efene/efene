# efene

Alternative syntax for the Erlang Programming Language focusing on simplicity, ease of use and programmer UX.

Visit [efene.org](https://efene.org) for documentation and [quickstart](guides/quickstart.md)

## Build

    rebar3 compile

## Use

For users we provide a [rebar3 plugin](guides/rebar-plugin.md) if you are developing there's a simple escript to use efene while developing:

    rebar3 escriptize

    ./_build/default/bin/efene beam file.fn
    ./_build/default/bin/efene rawlex file.fn
    ./_build/default/bin/efene lex file.fn
    ./_build/default/bin/efene ast file.fn
    ./_build/default/bin/efene mod file.fn
    ./_build/default/bin/efene erl file.fn
    ./_build/default/bin/efene erlast file.fn

### Formatting

Pretty print efene source as efene (a formatter):

    ./_build/default/bin/efene fmt file.fn

Pretty print Erlang source as efene (translate `.erl` to efene):

    ./_build/default/bin/efene fmt-erlang file.erl

## License

[APL 2.0](https://www.apache.org/licenses/LICENSE-2.0.html), see LICENSE file for details

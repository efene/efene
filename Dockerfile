FROM erlang:22.0.7

# Pin rebar3 to a version contemporaneous with the last commit (June 2019)
RUN set -eux; \
    curl -fsSL -o /usr/local/bin/rebar3 \
        https://github.com/erlang/rebar3/releases/download/3.12.0/rebar3; \
    chmod +x /usr/local/bin/rebar3; \
    rebar3 --version

WORKDIR /efene
COPY . .

# Build the escript (fetches hex deps, runs leex/yecc, compiles)
RUN rebar3 escriptize

# Default: show the built escript works
CMD ["/efene/_build/default/bin/efene"]

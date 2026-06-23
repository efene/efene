# Build environment for efene.
# OTP_VERSION is bumped one major at a time as the codebase is updated;
# each value here is a baseline that builds with no warnings or errors.
# The official erlang image bundles a compatible rebar3 for each OTP release.
ARG OTP_VERSION=23
FROM erlang:${OTP_VERSION}

WORKDIR /efene
COPY . .

# Build the escript (fetches hex deps, runs leex/yecc, compiles)
RUN rebar3 escriptize

# Default: show the built escript works
CMD ["/efene/_build/default/bin/efene"]

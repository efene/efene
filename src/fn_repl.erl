-module(fn_repl).
-export([main/0, start/0, pprint_data/1]).

start() ->
 spawn(fun main/0).

loop(Bindings) ->
  case io:get_line(">>> ") of
      eof ->
          io:format("~nBye!~n");
      Input ->
          case handle_input(Input, Bindings) of
              {ok, NewBindings} ->
                  loop(NewBindings)
          end
  end.

handle_input(Input, Bindings) ->
    case string:strip(string:strip(Input, both, $\n)) of
        "" -> {ok, Bindings};
        _Other ->
            case str_to_erl_ast(Input, "repl") of
                {ok, {[Ast], _State}} ->
                    try
                        case erl_eval:expr(Ast, Bindings,
                                           {value, fun lfun_value_handler/2},
                                           {value, fun nlfun_value_handler/2}) of
                            {value, Value, B1} ->
                                print(Value),
                                {ok, B1};
                            Other1 ->
                                io:format("error: ~p~n", [Other1]),
                                {ok, Bindings}
                        end
                    catch
                        T:E:S ->
                            io:format("~p: ~p~n~n", [T, E]),
                            pprint_strace(S),
                            {ok, Bindings}
                    end;
                Other2 ->
                    print(Other2),
                    {ok, Bindings}
            end
    end.

lfun_value_handler(help, []) -> help();
lfun_value_handler(i, []) -> c:i();
lfun_value_handler(i, [Pids]) -> c:i(Pids);
lfun_value_handler(l, [M]) -> c:l(M);
lfun_value_handler(cd, [Dir]) -> c:cd(Dir);
lfun_value_handler(ec, [F]) -> c:c(F);
lfun_value_handler(ec, [F, Os]) -> c:c(F, Os);
lfun_value_handler(m, []) -> c:m();
lfun_value_handler(pwd, []) -> c:pwd();
lfun_value_handler(flush, []) -> c:flush();
lfun_value_handler(regs, []) -> c:regs();
lfun_value_handler(ls, []) -> c:ls();
lfun_value_handler(ls, [Dir]) -> c:ls(Dir);
lfun_value_handler(q, []) ->
    c:q(),
    io:format("~nBye!~n"),
    timer:sleep(5000); % to avoid printing the next ">>>"
lfun_value_handler(clear, []) ->
    io:format("\e[H\e[J");
lfun_value_handler(Name, Arguments) ->
    throw({not_defined, {Name, Arguments}}).

nlfun_value_handler({Mod, Fun}, Arguments) ->
    erlang:apply(Mod, Fun, Arguments).

main() ->
    io:format("efene shell (call q() to quit, help() for help, Ctrl+g for Job Control Mode)~n~n"),
    Bindings = erl_eval:new_bindings(),
    loop(Bindings).

print({error, _}=Error) ->
    Reason = fn_error:normalize(Error),
    io:format("error:~s~n", [Reason]);
print(Data) ->
    io:format("~s~n", [pprint_data(Data)]).

str_to_erl_ast(String, Module) ->
    State0 = fn_to_erl:new_state(Module, "repl"),
    State = State0#{level => 1},

    case efene:str_to_ast(String) of
        {ok, Ast} -> {ok, fn_to_erl:ast_to_ast(Ast, State)};
        Other -> Other
    end.

pprint_strace(Strace) ->
    Lines = lists:map(fun ({ModName, FunName, Arity, Props}) ->
                              File = proplists:get_value(file, Props, "?"),
                              Line = proplists:get_value(line, Props, 0),
                              Args = [ModName, FunName, Arity, File, Line],
                              io_lib:format("~p.~p:~p ~s:~p", Args)
              end, Strace),
    Trace = string:join(Lines, "\n"),
    io:format("~s~n", [Trace]).

pprint_data(V) when is_binary(V) ->
    io_lib:format("'~s'", [V]);
pprint_data({V}) ->
    io_lib:format("(~s,)", [pprint_data(V)]);
pprint_data(V) when is_tuple(V) ->
    Items = lists:map(fun pprint_data/1, tuple_to_list(V)),
    CsItems = string:join(Items, ", "),
    io_lib:format("(~s)", [CsItems]);
pprint_data(V) when is_list(V) ->
    IsPrintable = io_lib:printable_unicode_list(V),
    if IsPrintable ->
           % TODO: escape quotes
           io_lib:format("\"~s\"", [V]);
       true ->
           Items = lists:map(fun pprint_data/1, V),
           CsItems = string:join(Items, ", "),
           io_lib:format("[~s]", [CsItems])
    end;
pprint_data(M) when is_map(M) ->
    Items = lists:map(fun ({K, V}) ->
                             io_lib:format("~s: ~s", [pprint_data(K), pprint_data(V)])
                     end, maps:to_list(M)),
    CsItems = string:join(Items, ", "),
    io_lib:format("{~s}", [CsItems]);
pprint_data(V) ->
    io_lib:format("~p", [V]).

help() ->
    io:put_chars(<<"\nefene shell built-in functions\n\n"
                   "b()        -- display all variable bindings\n"
                   "c(File)    -- compile and load code in <file>\n"
                   "cd(Dir)    -- change working directory to <dir>\n"
                   "clear()    -- clear the the REPL output\n"
                   "ec(File)   -- compile and load code in erlang <file>\n"
                   "help()     -- help info\n"
                   "i()        -- information about the system\n"
                   "l(Module)  -- load or reload <module>\n"
                   "ls()       -- list files in the current directory\n"
                   "ls(dir)    -- list files in directory <dir>\n"
                   "m()        -- which modules are loaded\n"
                   "m(Mod)     -- information about module <mod>\n"
                   "pwd()      -- print working directory\n"
                   "q()        -- quit - shorthand for init:stop/0\n"
                   "flush()    -- flushes all messages sent to the shell\n"
                   "regs()     -- information about registered processes\n\n">>).


% ------------------------------------------------------------------------------
% MODE: verbosity_value(Level,Value)
% SEMANTICS: Possible log levels in descending order
% (lower levels include higher ones):

% 0) OFF:        no logs published
verbosity_value(off,0).
% 1) ERROR:      error messages
verbosity_value(error,1).
% 2) WARNING:    warnings
verbosity_value(warning,2).
% 3) INFO:       basic info messages
verbosity_value(info,3).
% 4) FINE:       logs on learning input and output
verbosity_value(fine,4).
% 5) FINER:      logs on main learning cycle
verbosity_value(finer,5).
% 6) FINEST:     logs published by subsidiary learning procedures
verbosity_value(finest,6).
% 7) DEBUGGING:  debugging information
verbosity_value(debugging,7).

% abalearn_log/2
abalearn_log(MsgLevel,G) :-
  lopt(verbosity(Level)),
  ( verbosity_value(MsgLevel,MsgValue) ->
    ( (MsgValue =< Level) ->
      (
        current_output(OldStream), % save current output stream
        lopt(log_stream(LogStream)), % retrieve log stream
        set_output(LogStream),     % set the current output to be the log stream
        call(G),                   % call the call that produces the log entry
        flush_output(LogStream),
        set_output(OldStream)      % restore the old output stream
      )
    ;
      true
    )
  ;
    abalearn_error((write(Level), write(' is not a valid value for verbosity.')))
  ).

% abalearn_error/1
abalearn_error(Error) :-
  % close the current input stream
  told,
  tell(user_error),
  nl, write('[ABALearn] ERROR: '), call(Error), nl, nl,
  told,
	halt(1).
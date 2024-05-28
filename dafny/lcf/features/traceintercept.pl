prolog_trace_interception(Port, Frame, Choice, continue) :-
    write("port="), write(Port),

    % Frame attributes.
    prolog_frame_attribute(Frame, level, Level),
    write(" level="), write(Level),

    nl,

    prolog_frame_attribute(Frame, has_alternatives, HasAlternatives),
    write("\thas_alternatives="), writeln(HasAlternatives),

    prolog_frame_attribute(Frame, goal, Goal),
    write("\tgoal="), writeln(Goal),

    (
        prolog_frame_attribute(Frame, clause, ClauseRef)
        ->
            write("\tclause="), writeln(ClauseRef),

            clause_property(ClauseRef, file(File)),
            clause_property(ClauseRef, line_count(LineCount)),
            write("\tloc="), write(File), write(":"), writeln(LineCount),

            clause_info(ClauseRef, _File, _TermPos, _VarOffsets, [head(Head), body(Body), variable_names(Bindings)]),
            % write("\tfile="), writeln(File),
            % write("\tterm_pos="), writeln(TermPos),
            write("\thead="), writeln(Head),
            write("\tbody="), writeln(Body),
            write("\tbindings="), writeln(Bindings)

        ;
            true
    ),

    write_frame_arguments(Frame),

    prolog_frame_attribute(Frame, predicate_indicator, PredicateIndicator),
    write("\tpredicate_indicator="), writeln(PredicateIndicator),

    % Choice attributes.
    write("\tchoice="), writeln(Choice),

    prolog_choice_attribute(Choice, parent, Parent),
    write("\tchoice_parent="), writeln(Parent),

    prolog_choice_attribute(Choice, frame, ChoiceFrame),
    write("\tchoice_frame="), writeln(ChoiceFrame),

    prolog_choice_attribute(Choice, type, ChoiceType),
    write("\tchoice_type="), writeln(ChoiceType),

    nl.

write_frame_arguments(Frame) :-
    prolog_frame_attribute(Frame, goal, Goal),
    (   Goal = _:Head
    ->  functor(Head, _, Arity)
    ;   functor(Goal, _, Arity)
    ),
    write("\tarity="), writeln(Arity),
    write_frame_arguments(0, Arity, Frame).

write_frame_arguments(Arity, Arity, _) :- !.

write_frame_arguments(I, Arity, Frame) :-
    NI is I + 1,
    prolog_frame_attribute(Frame, argument(NI), Argument),
    write("\targument="), writeln(Argument),
    write_frame_arguments(NI, Arity, Frame).

% Alternative
% Value is unified with an integer reference to the local stack frame in which
% execution is resumed if the goal associated with Frame fails. Fails if the
% frame has no alternative frame.

% Goal
% Value is unified with the goal associated with Frame. If the definition module
% of the active predicate is not the calling context, the goal is represented as
% <module>:<goal>. Do not instantiate variables in this goal unless you know
% what you are doing! Note that the returned term may contain references to the
% frame and should be discarded before the frame terminates.245

% Parent_goal
% Parent_goal(-Parent)
% If Value is instantiated to a callable term, find a frame executing the
% predicate described by Value and unify the arguments of Value to the goal
% arguments associated with the frame. This is intended to check the current
% execution context. The user must ensure the checked parent goal is not removed
% from the stack due to last-call optimisation and be aware of the slow
% operation on deeply nested calls.  The variant parent_goal(-Parent) unifies
% the frame reference of the parent of the found frame with Parent. That allows
% for finding frames higher up in the stack running the same goal.

% Predicate_indicator
% Similar to goal, but only returning the [<module>:]<name>/<arity> term
% describing the term, not the actual arguments. It avoids creating an illegal
% term as goal and is used by the library library(prolog_stack).

% Clause
% Value is unified with a reference to the currently running clause. Fails if
% the current goal is associated with a foreign (C) defined predicate. See also
% nth_clause/3 and clause_property/2.

% Parent
% Value is unified with an integer reference to the parent local stack frame of
% Frame. Fails if Frame is the top frame.

% Context_module
% Value is unified with the name of the context module of the environment.

% Top
% Value is unified with true if Frame is the top Prolog goal from a recursive call back from the foreign language; false otherwise.

% Hidden
% Value is unified with true if the frame is hidden from the user, either
% because a parent has the hide-childs attribute (all system predicates), or the
% system has no trace-me attribute.

% Skipped
% Value is true if this frame was skipped in the debugger.

% Pc
% Value is unified with the program pointer saved on behalf of the parent goal
% if the parent goal is not owned by a foreign predicate or belongs to a
% compound meta-call (e.g., call((a,b))).

% Argument(N)
% Value is unified with the N-th slot of the frame. Argument 1 is the first
% argument of the goal. Arguments above the arity refer to local variables.
% Fails silently if N is out of range.

% ------------------------------------

node(n0).
node(n1).
node(n2).
node(n3).
edge(n1, n3).
edge(n1, n2).
edge(n0, n1).
source(n0).
destination(n3).
connected(A, B) :- edge(A, B).
connected(A, B) :- edge(A, M), connected(M, B).
query(S, D) :- source(S), destination(D), connected(S, D).
go :- forall(once(query(S, D)), (write(S), write(D), nl)).

% Facts.

namePermitted("auth.edu.gr").
namePermitted("auth.gr").

% Rules.
% std:count(NameChars, '*', 0),
% string_chars(Name, NameChars),
nameValid(Name) :-
    sub_string(Name, 0, 1, _, FirstChar),
    FirstChar \= ".",
    sub_string(Name, _, 1, 0, LastChar),
    LastChar \= ".".

namesValid(Names) :- forall(member(Name, Names), nameValid(Name)).

acceptName(Name) :-
    findall(PermittedName, namePermitted(PermittedName), PermittedNames),
    namesValid(PermittedNames),
    member(Name, PermittedNames).

% Goal.
go :- acceptName("auth.gr").

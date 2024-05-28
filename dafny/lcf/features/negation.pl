node("n0").
node("n1").
node("n2").
node("n3").

node("m0").
node("m1").
node("m2").
node("m3").

edge("n1", "n3").
edge("n1", "n2").
edge("n0", "n1").

edge("m1", "m3").
edge("m1", "m2").
edge("m0", "m1").

source("n0").
avoid("m0").

% Connectivity rules.
connected(A, B) :- edge(A, B).
connected(A, B) :- edge(A, M), connected(M, B).

query(N) :- source(S), connected(S, N), avoid(A), \+connected(N, A).
go :- forall(query(N), (write(N), nl)).

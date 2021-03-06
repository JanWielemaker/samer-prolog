:- module(treeutils, [tree_yield/3, convert_tree/2, maptree/3, print_tree/1, print_ltree/1, print_and_dump/3]).

:- use_module(library(callutils), [mr/5]).
:- use_module(library(data/tree), [print_tree/1, maptree/3]).
:- use_module(library(data/pair), [snd/2]).

print_and_dump(D,Memo,T) :- print_ltree(T), call(D,Memo).

print_ltree(T) :-
   once(convert_tree(T,T1)),
   once(print_tree(T1)).


% this handles various kinds of trees.
convert_tree(leaf(X), node(l(X),[])).
convert_tree(node(Subtrees), node(n, Ts)) :-
   maplist(convert_tree, Subtrees, Ts).
convert_tree(lnode(GenSubtrees), node(N, Ts)) :-
   call(GenSubtrees, Subtrees),
   maplist(convert_tree, Subtrees, Ts),
   label_node(Ts,N).
convert_tree(lnode(Label,GenSubtrees), node(N, Ts)) :-
   % writeln(expanding:Label),
   call(GenSubtrees, Subtrees),
   maplist(convert_tree, Subtrees, Ts),
   label_node(Ts,Label,N).

convert_tree(lwnode(Label,GenSubtrees), node(N, Ts)) :-
   % writeln(expanding:Label),
   call(GenSubtrees, Subtrees),
   maplist(convert_wtree, Subtrees, Ts),
   label_node(Ts,Label,N).

convert_wtree(W-T1, node(W-L,C)) :- convert_tree(T1,node(L,C)).

label_node([],f).
label_node([_|_],n).

label_node([],L,L:f).
label_node([_|_],L,L:n).

tree_yield(leaf(X)) --> [X].
tree_yield(node(Subtrees)) --> foldl(tree_yield, Subtrees).
tree_yield(lnode(Gen)) --> {call(Gen, Subtrees)}, foldl(tree_yield, Subtrees).
tree_yield(lnode(_,Gen)) --> {call(Gen, Subtrees)}, foldl(tree_yield, Subtrees).
tree_yield(lwnode(_,Gen)) --> {call(Gen, Dist)}, foldl(mr(snd,tree_yield), Dist).

user:portray(node(W-L)) :- format('(~3g)─~p',[W,node(L)]).
user:portray(node(L:n)) :- print(L).
user:portray(node(L:f)) :- print(L), print(node(f)).

user:portray(node(n)).
user:portray(node(f)) :- write('|').
user:portray(node(l(X:P))) :- format('~p:~3g',[X,P]).
user:portray(node(l(X))) :- write('<'), print(X).


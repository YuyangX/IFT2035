%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :-
    %% Ugly hack, âmes sensibles s'abstenir.
    (predicate_property(new_atom/2, built_in);    % Older GNU Prolog
     predicate_property(new_atom(_,_), built_in)) % Newer GNU Prolog
    -> new_atom(X, A);
    gensym(X, A).
%% Pas besoin de regarder les codes en-dessus.
debug_print(E) :- write(user_error, E), nl(user_error).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Description de la syntaxe des termes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Ces règles sont inutiles en soit, elle ne servent qu'à documenter pour
%% vous la forme des termes du langage H2035, ainsi que vous montrer quelques
%% primitives de Prolog qui peuvent vous être utiles dans ce TP, telles que
%% `=..`.

%% wf_type(+T)
%% Vérifie que T est un type syntaxiquement valide.
wf_type(int).
wf_type(bool).
wf_type(list(T)) :- wf_type(T).
wf_type((T1 -> T2)) :- wf_type(T1), wf_type(T2).
wf_type(Alpha) :- identifier(Alpha).
wf_type(forall(X,T)) :- atom(X), wf_type(T).
wf_type(X) :- var(X). %Une métavariable, utilisée pendant l'inférence de type.

%% wf(+E)
%% Vérifie que E est une expression syntaxiquement valide.
wf(X) :- integer(X).
wf(X) :- identifier(X).                   %Une constante ou une variable.
wf(lambda(X, E)) :- identifier(X), wf(E). %Une fonction.
wf(app(E1, E2)) :- wf(E1), wf(E2).        %Un appel de fonction.
wf(if(E1, E2, E3)) :- wf(E1), wf(E2), wf(E3).
wf((E : T)) :- wf(E), wf_type(T).
wf(?).                                  %Infère le code.
wf(E) :- E =.. [Head|Tail],
         (Head = let -> wf_let(Tail);
          identifier(Head), wf_exps(Tail)).

%% f(x1,x2) =.. [f, x1, x2]

%% identifier(+X)
%% Vérifie que X est un identificateur valide, e.g. pas un mot réservé.
identifier(X) :- atom(X),
                 \+ member(X, [lambda, app, if, let, (:), (?)]).

wf_exps([]).
wf_exps([E|Es]) :- wf(E), wf_exps(Es).

wf_let([E]) :- wf(E).
wf_let([Rdecl|Tail]) :- wf_rdecl(Rdecl), wf_let(Tail).

wf_rdecl([]).
wf_rdecl(D) :- wf_decl(D).
wf_rdecl([D|Ds]) :- wf_decl(D), wf_rdecl(Ds).

wf_decl(X = E) :-
    wf(E),
    (identifier(X);
     X =.. [F|Args], identifier(F), wf_args(Args)).

wf_args([]).
wf_args([Arg|Args]) :- wf_args(Args), identifier(Arg).

%%%%%% ELABORATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% elaborate(+Env, +Exp, ?Type, -NewExp)
%% Infère/vérifie le type de Exp, élimine le sucre syntaxique, et remplace
%% les variables par des indexes de deBruijn.
%% Note: Le cut est utilisé pour éviter de tomber dans la dernière clause
%% (qui signale un message d'erreur) en cas d'erreur de type.
elaborate(_, E, _, _) :-
    var(E), !, 
    debug_print(elaborate_nonclos(E)), fail.
elaborate(_, N, T, N) :- number(N), !, T = int.
elaborate(Env, lambda(X,E), T, lambda(DE)) :-
    !, elaborate([(X,T1)|Env], E, T2, DE), T = (T1 -> T2).

elaborate(Env, app(F, Arg), T, app(DF, DArg)) :-
    !, elaborate(Env, F, (T1 -> T2), DF),
    %!, elaborate(Env, F, T3, DF), write(T3),
    elaborate(Env, Arg, T1, DArg), T = T2.

elaborate(Env, if(E1, E2, E3), T, if(DE1, DE2, DE3)) :- 
    !, elaborate(Env, E1, bool, DE1), elaborate(Env, E2, T1, DE2), 
    elaborate(Env, E3, T1, DE3), T = T1.

elaborate(Env, +(N1, N2), T, app(app(var(Idx), DN1), DN2)) :-
    !, elaborate(Env, N1, int, DN1), elaborate(Env, N2, int, DN2),
    T = int, find_index(Env, (+), Idx).

elaborate(Env, cons(Fst, Res), T, app(app(var(Idx), DFst), DRes)) :-
    !, elaborate(Env, Fst, T1, DFst), elaborate(Env, Res, _, DRes),
    T = list(T1), find_index(Env, cons, Idx).

elaborate(Env, empty(List), bool, app(var(Idx), Dlist)) :- 
    !, elaborate(Env, List, _, Dlist), find_index(Env, empty, Idx).

elaborate(Env, car(cons(Fst, Res)), T, app(var(Idx), Dlist)) :-
    !, elaborate(Env, cons(Fst, Res), _, Dlist), elaborate(Env, Fst, T, _),
    find_index(Env, car, Idx).

elaborate(Env, cdr(cons(Fst, Res)), T, app(var(Idx), Dlist)) :-
    !, elaborate(Env, cons(Fst, Res), _, Dlist), elaborate(Env, Res, T, _),
    find_index(Env, cdr, Idx).

%%%%%%%%%%%%%% elaborates pour "let" sans récursion mutuelle %%%%%%%%%%%%%%%%%
%% Elabore le "let" sans sucre syntaxique, "let([decl], e)", en utilisant 
%% la règle "eliminate_syntactic_sugar_1".
elaborate(Env, let([Identificateur = Body], Exp), T, let([DBody], DExp)) :- 
    !, Identificateur =.. List, length(List, Len),
    % Si l'identificateur est de forme "name = body"
    Len = 1 -> 
    elaborate([(Identificateur, T1)|Env], Body, T1, DBody), write(T1), write(Body),
    elaborate([(Identificateur, T1)|Env], Exp, T, DExp), !;
    % Si l'identificateur est de forme "name(var1, ..., varn) = body"
    Identificateur =.. List, List = [Fst|Res],
    eliminate_syntactic_sugar_1(Res, Body, RawBody),    
    elaborate([(Fst, T2)|Env], RawBody, T2, DBody), write(T2),
    elaborate([(Fst, T2)|Env], Exp, T, DExp), !.

%% Elabore le "let" avec le sucre syntaxique "let(decl, e)".
elaborate(Env, let(Identificateur = Body, Exp), T, let([DBody], DExp)) :- 
    !, elaborate(Env, let([Identificateur = Body], Exp), T, let([DBody], DExp)).

%% Elabore le "let" avec le sucre syntaxique "let(d1, ..., dn, e)", en utilisant 
%% la règle "eliminate_syntactic_sugar_3".
elaborate(Env, Lets, T, DLets) :-
    Lets =.. [Fst|Res], Fst = let, !,
    eliminate_syntactic_sugar_3(Res, RawLet),
    elaborate(Env, RawLet, T, DLets).
%%%%%%%%%%%% Fin des elaborates pour "let" sans récursion mutuelle %%%%%%%%%%%

%% Renvoie une variable avec indice de De Bruijn.
elaborate(Env, Var, T, var(Idx)) :- 
    % Identifie si Var est bien une seule variable.
    Var =.. List, length(List, Len), Len = 1, !,
    find_var(Env, Var, T, Idx), write(1), write(Idx+8), write(T).
    %find_index(Env, Var, Idx), find_type(Env, Var, T).

%% Elimine le sucre syntaxique de l'appel de fonction, qui a la forme
%% f(e1, ..., en), et renvoie la forme correspondante sans identificateur,
%% en utilisant la règle "eliminate_syntactic_sugar_2".
elaborate(Env, CallFonc, T, DCallFonc) :-
    % S'assure que ce ne soit pas un "let". 
    CallFonc =.. [Fst|Res], \+(Fst = let), !, 
    eliminate_syntactic_sugar_2(Fst, Res, RawCallFonc), 
    elaborate(Env, RawCallFonc, T, DCallFonc).

%% ¡¡ REMPLIR ICI !!
elaborate(_, E, _, _) :-
    debug_print(elab_unknown(E)), fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%% Règles auxiliaires %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
find_var([(Ele, Type)|_], Ele, Type, 0) :- !.
find_var([_|ResEnv], Ele, Type, Idx) :-
    find_var(ResEnv, Ele, Type, Idx1), Idx is Idx1 + 1. 

%% find_index(+Env, +Ele, -Idx)
%% Renvoie la position de l'élément dans l'environnement env0.
find_index([(Ele, _)|_], Ele, 0) :- !.
find_index([_|ResEnv], Ele, Idx) :- 
    find_index(ResEnv, Ele, Idx1), Idx is Idx1 + 1.

%% find_type(+Env, +Ele, -Type)
%% Renvoie le type de l'élément dans l'environnement env0.
find_type([(Ele, Type)|_], Ele, Type) :- !.
find_type([_|ResEnv], Ele, Type) :- find_type(ResEnv, Ele, Type).

%% eliminate_syntactic_sugar_1(+ArgList, +Body, -RawBody)
%% Eliminer le sucre syntaxique de la définition de fonction, qui a
%% la forme f(x1, ..., xn).
eliminate_syntactic_sugar_1([FstArg|[]], Body, RawBody) :-
    RawBody = lambda(FstArg, Body).
eliminate_syntactic_sugar_1([FstArg|ResArgs], Body, RawBody) :-
    RawBody = lambda(FstArg, Res), eliminate_syntactic_sugar_1(ResArgs, Body, Res).

%% eliminate_syntactic_sugar_2(+Name, +ActualArgs, -RawExp)
%% Eliminer le sucre syntaxique de l'appel de fonction, qui a 
%% la forme f(e1, ..., en).
eliminate_syntactic_sugar_2(Name, [FstArg|[]], RawExp) :- 
    RawExp = app(Name, FstArg).
eliminate_syntactic_sugar_2(Name, [FstArg|ResArgs], RawExp) :- 
    eliminate_syntactic_sugar_2(Name, [FstArg], Res), 
    eliminate_syntactic_sugar_2(Res, ResArgs, RawExp).    

%% eliminate_syntactic_sugar_3(+LetElem, -RawLet)
%% Eliminer le sucre syntaxique de "let", qui a la forme let(d1, ..., dn, e).
eliminate_syntactic_sugar_3([FstLet|ExpList], RawLet) :-
    length(ExpList, Len), Len = 1, !, ExpList = [Exp], RawLet = let(FstLet, Exp).
eliminate_syntactic_sugar_3([FstLet|ResLets], RawLet) :-
    RawLet = let(FstLet, Res), eliminate_syntactic_sugar_3(ResLets, Res).
%%%%%%%%%%%%%%%%%%%%%%%%% Fin de règles auxiliaires %%%%%%%%%%%%%%%%%%%%%%%%%%

%% Ci-dessous, quelques prédicats qui vous seront utiles:
%% - instantiate: correspond à la règle "σ ⊂ τ" de la donnée.
%% - freelvars: correspond au "fv" de la donnée.
%% - generalize: fait le travail du "gen" de la donnée.

%% instantiate(+PT, -T)
%% Choisi une instance d'un type polymorphe PT.
instantiate(V, T) :- var(V), !, T = V.
instantiate(forall(X,T), T2) :-
    !, substitute(T, X, _, T1), instantiate(T1, T2).
instantiate(T, T).              %Pas de polymorphisme à instancier.


%% substitute(+Type1, +TVar, +Type2, -Type3)
%% Remplace TVar par Type2 dans Type1, i.e. `Type3 = Type1[Type2/TVar]`.
substitute(T1, _, _, T3) :- var(T1), !, T3 = T1.
substitute(X, X, T, T) :- !.
substitute(T1, X, T2, T3) :-
    %% T1 a la forme Head(Tail).  E.g. Head='->' et Tail=[int,int].
    %% Ça peut aussi être Head='int' et Tail=[].
    T1 =.. [Head|Tail],
    mapsubst(Tail, X, T2, NewTail),
    T3 =.. [Head|NewTail].

%% Applique `substitute' sur une liste.
mapsubst([], _, _, []).
mapsubst([T1|T1s], X, T2, [T3|T3s]) :-
    substitute(T1, X, T2, T3), mapsubst(T1s, X, T2, T3s).

%% freelvars(+E, -Vs)
%% Trouve toutes les variables logiques (i.e. variables Prolog) non
%% instanciées qui apparaissent dans le terme Prolog E, et les renvoie
%% dans la liste Vs.
freelvars(E, Vs) :- freelvars([], E, Vs).

%% freelvars(+Vsi, +E, -Vso)
%% Règle auxiliaire de freelvars/2.
freelvars(Vsi, V, Vso) :-
    var(V), !,
    (member(V, Vsi) -> Vso = Vsi; Vso = [V|Vsi]).
freelvars(Vsi, E, Vso) :-
    (E = [T|Ts], !; E =.. [_,T|Ts]) ->
        freelvars(Vsi, T, Vs1),
        freelvars(Vs1, Ts, Vso);
    Vso = Vsi.

%% generalize(+FVenv, +Env, -GEnv)
%% Généralise un morceau d'environnement Env en un morceau d'environnement
%% GEnv où chaque variable a été rendue aussi polymorphe que possible.
%% FVenv est la liste des variables libres de l'environnement externe.
generalize(_, [], []).
generalize(FVenv, [(X,T)|DeclEnv], [(X,GT)|GenEnv]) :-
    freelvars(T,FVs),
    gentype(FVenv, FVs, T, GT),
    generalize(FVenv, DeclEnv, GenEnv).

%% gentype(+FVenv, +FV, +T, -GT)
%% Généralise le type T en un type GT aussi polymorphe que possible.
%% FVenv est la liste des variables libres de l'environnement, et FV
%% est la liste des variables libres de T.
gentype(_, [], T, T).
gentype(FVenv, [V|Vs], T, GT) :-
    gentype(FVenv, Vs, T, GT1),
    (member(V, FVenv) -> GT = GT1;
     genatom(t, V), GT = forall(V, T)).


%%%%%% EVALUATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% eval(+Env, +Exp, -Val)
%% Évalue Exp dans le context Env et renvoie sa valeur Val.
%% Note: Le cut est utilisé pour éviter de tomber dans la dernière clause
%% (qui signale un message d'erreur) en cas d'échec après l'évaluation,
%% i.e. pour distinguer le cas d'une expression que notre code ne couvre pas
%% des autres cas d'échec.
eval(_, E, _) :-
    var(E), !,
    debug_print(eval_nonclos(E)), fail.
eval(_, N, N) :- number(N), !.
eval(Env, var(Idx), V) :- !, nth_elem(Idx, Env, V).  % Env est juste une liste de valeurs plutot qu'une liste de paires
eval(Env, lambda(E), closure(Env, E)) :- !.
eval(Env, app(E1, E2), V) :- 
    !, eval(Env, E1, V1),
    eval(Env, E2, V2),
    apply(V1, V2, V).
eval(Env, if(E1, E2, E3), V) :-
    !, eval(Env, E1, true) -> eval(Env, E2, V); eval(Env, E3, V).
eval(Env, let([Exp], Body), V) :-
    !, eval([_|Env], Exp, DExp), eval([DExp|Env], Body, V).

%% ¡¡ REMPLIR ICI !!
eval(_, E, _) :-
    debug_print(eval_unknown(E)), fail.


%% apply(+Fun, +Arg, -Val)
%% Evaluation des fonctions et des opérateurs prédéfinis.
apply(closure(Env, Body), Arg, V) :- eval([Arg|Env], Body, V).
apply(builtin(BI), Arg, V) :- builtin(BI, Arg, V).
%% builtin(list, V, list(V)).
builtin((+), N1, builtin(+(N1))).
builtin(+(N1), N2, N) :- N is N1 + N2.
builtin(cons, X, builtin(cons(X))).
builtin(cons(X), XS, [X|XS]).
builtin(empty, X, Res) :- X = [] -> Res = true; Res = false.
builtin(car, [X|_], X).
builtin(cdr, [_|XS], XS).
builtin(cdr, [], []).

%% nth_elem(+I, +VS, -V)
%% Renvoie le I-ème élément de la liste Vs.
nth_elem(0, [V|_], V).
nth_elem(I, [_|Vs], V) :- I > 0, I1 is I - 1, nth_elem(I1, Vs, V).

%%%%%% TOP-LEVEL %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% env0(-Env)
%% Renvoie l'environnement initial combiné (types et valeurs).
env0([((+),   (int -> int -> int),                  builtin(+)),
      (true,  bool,                                 true),
      (false, bool,                                 false),
      (nil,   forall(t, list(t)),                   []),
      (cons,  forall(t, (t -> list(t) -> list(t))), builtin(cons)),
      (empty, forall(t, (list(t) -> bool)),         builtin(empty)),
      (car,   forall(t, (list(t) -> t)),            builtin(car)),
      (cdr,   forall(t, (list(t) -> list(t))),      builtin(cdr))]).

%% Extrait l'environnement de typage de l'environnement combiné.
get_tenv([], []).
get_tenv([(X,T,_)|Env], [(X,T)|TEnv]) :- get_tenv(Env, TEnv).

%% tenv0(-TEnv)
%% Renvoie l'environnment de types initial.
tenv0(TEnv) :- env0(Env), get_tenv(Env, TEnv).

%% Extrait l'environnement de valeurs de l'environnement combiné.
get_venv([], []).
get_venv([(_,_,V)|Env], [V|VEnv]) :- get_venv(Env, VEnv).

%% venv0(-VEnv)
%% Renvoie l'environnment de valeurs initial.
venv0(VEnv) :- env0(Env), get_venv(Env, VEnv).

%% runelab(+Prog, -Type, -Elab)
%% Elabore Prog et renvoie le code élaboré et son type.
runelab(E, T, El) :- tenv0(TEnv), elaborate(TEnv, E, T, El).

%% runeval(+Prog, -Type, -Val)
%% Type et exécute le programme Prog dans l'environnement initial.
runeval(E, T, V) :- tenv0(TEnv), elaborate(TEnv, E, T, DE),
                   !,
                   venv0(VEnv), eval(VEnv, DE, V).

%% Exemples d'usage:
%% runeval(1 + 2, T, V).
%% runeval(app(lambda(x,x+1),3), T, V).
%% runeval(app(lambda(f,f(3)),lambda(x,x+1)), T, V).
%% runeval(let([x = 1], 3 + x), T, V).
%% runeval(let(f(x) = x+1, f(3)), T, V).
%% runeval(let([x = 1, x = lambda(a, a + 1)], (3 + x(x))), T, V).
%% runeval(cons(1,nil), T, V).
%% runeval(?(1,nil), T, V).
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(?(42,?(41,?(40,nil))))
%%             + length(cons(1,nil))),
%%         T, V).
%% runeval(let([length(x) = if(empty(x), 0, 1 + length(cdr(x)))],
%%             length(?(42,?(41,?(40,nil)))) + length(cons(4,nil))),
%%         T, V).
%%
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(?(42,?(41,?(40,nil))))
%%             + length(cons(true,nil))),
%%         T, V).

%% Exemples d'usage:
%% runeval(1 + 2, T, V).
3
%% runeval(app(lambda(x,x+1),3), T, V).
4
%% runeval(app(lambda(f,f(3)),lambda(x,x+1)), T, V).
4
%% runeval(let([x = 1], 3 + x), T, V).
4
%% runeval(let(f(x) = x+1, f(3)), T, V).
4
%% runeval(let([x = 1, x = lambda(a, a + 1)], (3 + x(x))), T, V).
5
%% runeval(cons(1,nil), T, V).
[1]
%% runeval(?(1,nil), T, V).
[1]
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(?(42,?(41,?(40,nil))))
%%             + length(cons(1,nil))),
%%         T, V).
4
%% runeval(let([length(x) = if(empty(x), 0, 1 + length(cdr(x)))],
%%             length(?(42,?(41,?(40,nil)))) + length(cons(4,nil))),
%%         T, V)
4
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(?(42,?(41,?(40,nil))))
%%             + length(cons(true,nil))),
%%         T, V).
4

%Exemple d'élaboration "/$%?&*(***&)&&&()()))((()()))_+_"¦thgfdarweqweee§§§§§aaaaaaasdfghjkzxcvbnµµµµµ­­­qqq
1 + 2	
%app(app(var(0), 1), 2)

app(lambda(x,x+1),3)	
%app(lambda(app(app(var(1), var(0)),1)),3)

app(lambda(f,f(3)),lambda(x,x+1))	
%app(lambda(app(var(0),3)),lambda(app(app(var(1), var(0)),1)))

let([x = 1], 3 + x)	
%let([1], app(app(var(1), 3), var(0)))

let(f(x) = x+1, f(3))	
%let([lambda(app(app(var(2), var(0)),1))], app(var(0), 3))

let([x = 1, x = lambda(a, a + 1)], (3 + x(x)))	
%let([1, lambda(app(app(var(3), var(0)), 1))], app(app(var(2), 3), app(var(0), var(1))))

lambda(x, x)
%lambda(var(0))
%forall(t, t -> t)

nil : list(bool)
%var(3)
%list(bool)

+(5)
%app(var(0), 5)
%int -> int

cons(1,nil)
%app(app(var(4), 1), var(3))
%list(int)

?(1,nil)
%app(app(var(4), 1), var(3)) (identique)
%list(int)


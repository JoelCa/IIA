animal(X) :- satisface(esta_vivo,X), satisface(puede_sentir,X), satisface(puede_moverse,X).
mamifero(X) :- animal(X), satisface(da_leche,X), satisface(tiene_pelo,X).
tigre(X) :- mamifero(X), satisface(come_carne,X).

:- dynamic si/1,no/1.
satisface(Atributo,_) :-
(
si(Atributo) -> true ;
(
no(Atributo) -> fail ;
pregunta(Atributo)
)
).
pregunta(A) :-
write('¿Tiene el animal este atributo?: '), write(A), write(' '), read(Resp), nl,
(
(Resp == s ; Resp == si ; Resp == sí) -> assert(si(A));
assert(no(A))
, fail).
animal :- adivina(Animal,_), write('El animal es: '), write(Animal), nl, borraResp.
adivina(tigre,X) :- tigre(X).
adivina(_,desconocido).

%Integrantes:
%Bonet, Javier
%Catacora, Joel
%Oviedo, Juan Manuel

deporte(x) :- satisface(se_entrena,X), satisface(es_saludable,X), satisface(esta_vigente,X).

deporte_olimpico(X) :- deporte(X), satisface(se_juega_en_las_olimpiadas,X).
tiene_numerosos_jugadores(X) :- deporte(X), satisface(al_menos_5_jugadores,X).
ambiente_cerrado(X) :- deporte(X), satisface(se_juega_en_ambiente_cerrado,X).
cesped(X) :- deporte(X), satisface(se_practica_sobre_cesped,X).
agua(X) :- deporte(X), satisface(se_practica_sobre_agua,X).


%DEPORTES

basquet(X) :- deporte_olimpico(X), tiene_numerosos_jugadores(X), ambiente_cerrado(X), satisface(se_utiliza_el_termino_canasta,X).

hockey(X) :- deporte_olimpico(X), tiene_numerosos_jugadores(X), cesped(X), satisface(se_usa_el_termino_bocha,X),satisface(se_usa_el_termino_corto,X).

futbol(X) :- deporte_olimpico(X), tiene_numerosos_jugadores(X), cesped(X), satisface(se_usa_el_termino_offside,X).

voley(X) :- deporte_olimpico(X), tiene_numerosos_jugadores(X), satisface(se_usa_el_termino_armador,X).

natacion(X) :- deporte_olimpico(X), agua(X), satisface(se_usan_antiparras,X).

boxeo(X) :- deporte_olimpico(X), ambiente_cerrado(X), satisface(se_usan_guantes,X).

tenis(X) :- deporte_olimpico(X), satisface(se_usa_raqueta,X).

ciclismo(X) :- deporte_olimpico(X), satisface(se_usa_bicicleta,X).

beisbol(X) :- tiene_numerosos_jugadores(X), cesped(X), satisface(se_usa_bate,X).

rugby(X) :- tiene_numerosos_jugadores(X), cesped(X), satisface(se_usa_el_termino_scrum,X).

ajedrez(X) :- ambiente_cerrado(X), satisface(se_usa_el_termino_jaque_mate,X).

surf(X) :- deporte(X), agua(X), satisface(se_usa_tabla,X).

bochas(X) :- deporte(X), satisface(se_usa_el_termino_bocha,X), satisface(se_juega_con_muchas_bolas,X).

tejo(X) :- deporte(X), satisface(se_puede_jugar_en_arena,X).

%FIN DEPORTES


:- dynamic si/1 ,no/1.


satisface(Atributo,_) :-
        (
         si(Atributo) -> true ;
         (
          no(Atributo) -> fail ;
          pregunta(Atributo)
         )
        ).

pregunta(A) :-
	write('El deporte tiene esta caracteristica?: '), write(A), write(' '), read(Resp), nl,
	(
         (Resp == s ; Resp == si ; Resp == yes) -> assert(si(A));
         assert(no(A)),
         fail
        ).

adivina(basquet,X) :- basquet(X).
adivina(hockey,X) :- hockey(X).
adivina(futbol,X) :- futbol(X).
adivina(voley,X) :- voley(X).
adivina(natacion,X) :- natacion(X).
adivina(boxeo,X) :- boxeo(X).
adivina(tenis,X) :- tenis(X).
adivina(ciclismo,X) :- ciclismo(X).
adivina(beisbol,X) :- beisbol(X).
adivina(rugby,X) :- rugby(X).
adivina(ajedrez,X) :- ajedrez(X).
adivina(surf,X) :- surf(X).
adivina(bochas,X) :- bochas(X).
adivina(tejo,X) :- tejo(X).
adivina(deporte_desconocido,_).

borraResp :- retractall(si(_)), retractall(no(_)).

deporte :- adivina(Deporte,_), write('El deporte es: '), write(Deporte), nl, borraResp.
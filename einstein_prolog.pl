hid(1).
hid(2).
hid(3).
hid(4).
hid(5).

nation(brit).
nation(swede).
nation(dane).
nation(norweigan).
nation(german).

color(green).
color(white).
color(yellow).
color(blue).
color(red).

pet(dog).
pet(birds).
pet(cats).
pet(horse).
pet(fish).

drink(tea).
drink(coffee).
drink(milk).
drink(beer).
drink(water).

smoke(pall_mall).
smoke(dunhill).
smoke(blend).
smoke(bluemaster).
smoke(prince).

right_of(X, Y) :- X is Y+1.
left_of(X, Y) :- right_of(Y, X).

next_to(X, Y) :- right_of(X, Y).
next_to(X, Y) :- left_of(X, Y).

rep(house(_,B1,C1,D1,E1,F1), house(_,B2,C2,D2,E2,F2)) :- 
      B1==B2,!
    ; C1==C2,!
    ; D1==D2,!
    ; E1==E2,!
    ; F1==F2.

distinct([]).
distinct([H|Xs]):- norep(H, Xs), distinct(Xs).
norep(H, []).
norep(H, [H1|Xs]) :- not(rep(H,H1)),norep(H, Xs).

safe_house(house(A,B,C,D,E,F)) :- hid(A), nation(B), color(C), pet(D), drink(E), smoke(F).
safe_street([]).
safe_street([H|Xs]) :- safe_house(H), safe_street(Xs).

solution(Street, FishOwner) :-
    Street = [
           house(1, Nationality1,  Color1,     Pet1,   Drinks1,    Smokes1),
           house(2, Nationality2,  Color2,     Pet2,   Drinks2,    Smokes2),
           house(3, Nationality3,  Color3,     Pet3,   Drinks3,    Smokes3),
           house(4, Nationality4,  Color4,     Pet4,   Drinks4,    Smokes4),
           house(5, Nationality5,  Color5,     Pet5,   Drinks5,    Smokes5)],
    member(house(_, brit,          _,          _,      _,          _           ), Street),
    member(house(_, swede,         _,          dog,    _,          _           ), Street),
    member(house(_, dane,          _,          _,      tea,        _           ), Street),
    member(house(A, _,             green,      _,      _,          _           ), Street),
    member(house(B, _,             white,      _,      _,          _           ), Street),
    left_of(A, B),
    member(house(_, _,             green,      _,      coffee,     _           ), Street),
    member(house(_, _,             _,          birds,  _,          pall_mall   ), Street),
    member(house(_, _,             yellow,     _,      _,          dunhill     ), Street),
    member(house(3, _,             _,          _,      milk,       _           ), Street),
    member(house(1, norweigan,     _,          _,      _,          _           ), Street),
    member(house(C, _,             _,          _,      _,          blend       ), Street),
    member(house(D, _,             _,          cats,   _,          _           ), Street),
    next_to(C, D),
    member(house(E, _,             _,          horse,  _,          _           ), Street),
    member(house(F, _,             _,          _,      _,          dunhill     ), Street),
    next_to(E, F),
    member(house(_, _,             _,          _,      beer,       bluemaster  ), Street),
    member(house(_, german,        _,          _,      _,          prince      ), Street),
    member(house(G, norweigan,     _,          _,      _,          _           ), Street),
    member(house(H, _,             blue,       _,      _,          _           ), Street),
    next_to(G, H),
    member(house(I, _,             _,          _,      _,          blend       ), Street),
    member(house(J, _,             _,          _,      water,      _           ), Street),
    next_to(I, J),
member(house(_, FishOwner, _, fish, _, _ ), Street), safe_street(Street) ,distinct(Street).

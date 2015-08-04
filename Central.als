open util/ordering[Time] -- ordenação dos tempos

sig Time{} -- objetos que representam momentos no tempo

sig Taxi{
regiao: one Regiao,
placa: one Placa,
status: Status -> Time -- o taxi só poderá ter um status por tempo, definir isso, pois o one foi retirado
}
sig Valido in Taxi {}

sig Placa{}
abstract sig Status {}
one sig Ocupado, Livre extends Status {}

one sig Central{
cadastrados: Taxi -> Time -- temos que fazer com que o número de taxi cadastrados seja obrigatoriamente maior que 1, pois para ter uma relação ternária retirei o some
}

abstract sig Regiao {}
one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}

sig Pessoa{
r: one Regiao,
taxi: Taxi -> Time -- uma pessoa só pode pegar um taxi em um tempo t, definir isso
}

fact{
--all t: Taxi | #(t.~taxi) <= 1 um taxi só pode ser ocupado por uma pessoa ?? isso é necessário?
all p: Placa | #(p.~placa) = 1 
all p: Pessoa, c: Central | p.taxi in c.cadastrados 
--all P: Pessoa, T: Taxi | (T in P.taxi) implies (T.regiao = P.r) uma pessoa só pode pegar o taxi da sua mesma região 
--all t: Taxi, p: Pessoa | (t in p.taxi) implies (t.status = Ocupado) se uma pessoa pegar um taxi ele mudará o status para ocupado, criar predicado
--all t: Taxi | (#(t.~taxi) = 0) implies (t.status = Livre) todo taxi sem pessoa está livre
-- tive que deixar comentado pois tinha feito todas essas relações como binárias, mas tem que se usar os predicados e funções para torná-las ternárias
}
pred show[]{
}
run show 

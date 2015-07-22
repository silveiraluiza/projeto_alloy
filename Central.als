open util/ordering[Time] -- ordenação dos tempos

sig Time{} -- objetos que representam momentos no tempo

sig Taxi{
regiao: one Regiao,
placa: one Placa,
status: one Status 
}
sig Valido in Taxi {}

sig Placa{}
abstract sig Status {}
one sig Ocupado, Livre extends Status {}

one sig Central{
cadastrados: some Taxi
}

abstract sig Regiao {}
one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}

sig Pessoa{
r: one Regiao,
taxi: one Taxi
}

fact{
all t: Taxi | #(t.~taxi) <= 1
all p: Placa | #(p.~placa) = 1 
all p: Pessoa, c: Central | p.taxi in c.cadastrados 
all P: Pessoa, T: Taxi | (T in P.taxi) implies (T.regiao = P.r) 
all t: Taxi, p: Pessoa | (t in p.taxi) implies (t.status = Ocupado)
all t: Taxi | (#(t.~taxi) = 0) implies (t.status = Livre)
}
pred show[]{
}
run show 

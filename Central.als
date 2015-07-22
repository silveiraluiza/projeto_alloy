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


abstract sig Regiao {}
one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}

sig Pessoa{
r: one Regiao,
taxi: one Taxi
}

fact{
all t: Taxi | #(t.~taxi) = 1
all p: Placa | #(p.~placa) = 1 
}
pred show[]{
}
run show 

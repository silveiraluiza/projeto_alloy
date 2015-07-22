open util/ordering[Time] -- ordenação dos tempos

sig Time{} -- objetos que representam momentos no tempo

sig Taxi{
regiao: one Regiao,
placa: one Placa

}

sig Placa{}
one sig TaxiOcupado, TaxiLivre extends Taxi {}
sig Valido in Taxi {}

abstract sig Regiao {}
one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}

sig Pessoa{
r: one Regiao,
taxi: one Taxi
}

fact{
all t: Taxi | #(t.~taxi) = 1
all p: Placa | #(p.~placa) = 1 
all R: Regiao, N: Norte, S: Sul, O: Oeste, C: Centro, L: Leste | R = N or R = S or R = O or R = C or R = L
}
pred show[]{
}
run show 

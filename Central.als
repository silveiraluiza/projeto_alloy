open util/ordering[Time] -- ordenação dos tempos

sig Time{} -- objetos que representam momentos no tempo

sig Taxi{
regiao: one Regiao,
placa: one Placa

}

sig Placa{}
sig Ocupado in Taxi {}

abstract sig Regiao {}
one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}

pred show[]{
}
run show 

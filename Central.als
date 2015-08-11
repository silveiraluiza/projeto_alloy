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

//------------------

// Define os status dos taxistas
pred init [t: Time]{
	t = first => Taxi.status.t = Livre -- Um sempre tem status inicial disponível
	t = first => no (Central.cadastrados).t  //a central inicia vazia 
}

// Todo taxista possui uma placa identificadora
pred todoTaxistaComPlaca[p1: Placa]{
	p1 in Taxi.placa
}

// Taxista possui apenas um status
pred taxistaPossuiApenas1Status[T: Taxi, t: Time]{
	#(T.status) . t = 1
	
}
pred taxiocupado[T:Taxi, t:Time, P: Pessoa]{
	(T in (P.taxi).t) implies ((T.status).t = Ocupado) 
}
// muda o status de taxi

pred AdcTaxiCentral[T1: Taxi, t,t': Time, C: Central]{
	T1 !in (C.cadastrados).t
	 ((C.cadastrados).t' = (C.cadastrados).t + T1)
}
//adiciona taxi a central, imitação do código do banco para teste, deu certo

pred PessoaUmTaxi[P: Pessoa, t: Time]{
# ((P.taxi).t) <= 1
}
//uma pessoa não pode ocupar dois taxis ao mesmo tempo

pred TaxiPertenceCentral[T: Taxi,C: Central,t: Time]{
	  T in (C.cadastrados).t
}
// Verifica se taxi pertence a central
fact traces{
	init[first]

// para quaisquer dois diferentes taxis, eles possuem cadastros distintos.
	all T: Taxi, T1: Taxi - T | #(T.placa & T1.placa) = 0 // não é necessário pois coloquei o one na placa
// Taxista possui apenas um status um status (disponivel ou ocupado)
	all T: Taxi, t: Time | taxistaPossuiApenas1Status[T,t] -- 0k
//	Todo taxista possui uma placa
	all P: Placa | todoTaxistaComPlaca[P] -- ok // também não é necessário por causa do one, talvez pode ser implementado como teste?
	all T: Taxi, P:Pessoa, t: Time | taxiocupado[T,t,P]
	all p: Placa | #(p.~placa) = 1 
	all p: Pessoa, c: Central | p.taxi in c.cadastrados 
	all P: Pessoa, t: Time|  PessoaUmTaxi[P,t]

	all T: Taxi, C: Central, t,t1: Time - first | 
		 TaxiPertenceCentral[T,C,t] <=>  TaxiPertenceCentral[T,C,t1]  


--all P: Pessoa, T: Taxi | (T in P.taxi) implies (T.regiao = P.r) uma pessoa só pode pegar o taxi da sua mesma região 
--all t: Taxi, p: Pessoa | (t in p.taxi) implies (t.status = Ocupado) se uma pessoa pegar um taxi ele mudará o status para ocupado, criar predicado
--all t: Taxi | (#(t.~taxi) = 0) implies (t.status = Livre) todo taxi sem pessoa está livre
-- tive que deixar comentado pois tinha feito todas essas relações como binárias, mas tem que se usar os predicados e funções para torná-las ternárias
}











run init for 6

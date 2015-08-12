open util/ordering[Time] -- ordenação dos tempos

sig Time{} -- objetos que representam momentos no tempo

sig Taxi{
regiao: one Regiao,
placa: one Placa,
status: Status -> Time, 
registro: Reg -> Time
}
abstract sig Reg {}
one sig Valido, Invalido extends Reg {}

sig Placa{}
abstract sig Status {}
one sig Ocupado, Livre extends Status {}

one sig Central{
cadastrados: Taxi -> Time 
}

abstract sig Regiao {}
one sig Norte, Sul, Leste, Oeste, Centro extends Regiao{}

sig Pessoa{
r: one Regiao,
taxi: Taxi -> Time 
}

//------------------

// Define os status dos taxistas e da central
pred init [t: Time]{
	 Taxi.status.t = Livre  //Um sempre tem status inicial disponível
	no (Central.cadastrados).t   //a central inicia vazia 
}

// Todo taxista possui uma placa identificadora
pred todoTaxistaComPlaca[p1: Placa]{
	p1 in Taxi.placa
}
//taxi pode levar apenas um passageiro, ok? 
pred TaxiUmaPessoa[T: Taxi, t: Time, P, P1: Pessoa]{
(T in (P.taxi).t) implies (T !in (P1.taxi).t)
}
// Taxista possui apenas um status
pred taxistaPossuiApenas1Status[T: Taxi, t: Time]{
	#(T.status) . t = 1
}
// Taxista possui apenas um Registro por unidade tempo
pred taxistaPossuiApenas1Reg[T: Taxi, t: Time]{
	#(T.registro) . t = 1
}
// muda o status de taxi
pred taxiocupado[T:Taxi, t:Time, P: Pessoa]{
	(T in (P.taxi).t) implies ((T.status).t = Ocupado) 
}

//adiciona taxi a central, imitação do código do banco para teste, deu certo
pred AdcTaxiCentral[T1: Taxi, t,t': Time, C: Central]{
	T1 !in (C.cadastrados).t
	 ((C.cadastrados).t' = (C.cadastrados).t + T1)
}
//uma pessoa não pode ocupar dois taxis ao mesmo tempo
pred PessoaUmTaxi[P: Pessoa, t: Time]{
	# ((P.taxi).t) <= 1
}
// Verifica se taxi pertence a central
pred TaxiPertenceCentral[T: Taxi,C: Central,t: Time]{
	  (T !in (C.cadastrados).t) || ((T.registro).t = Valido)
}
// em algum ponto do tempo o registro do taxi se tornará inválido
pred mudaValidade[T: Taxi, t0: Time, t1: Time]{
	((T.registro).t0 = Valido) implies (((T.registro).t1 = Valido) or ((T.registro).t1 = Invalido))
}
fact traces{
	init[first]
// Taxista possui apenas um status um status (disponivel ou ocupado)
	all T: Taxi, t: Time | taxistaPossuiApenas1Status[T,t]
// Taxista possui apenas um status um registro (válido ou não)
	all T: Taxi, t: Time | taxistaPossuiApenas1Reg[T,t]
// se um taxi estiver ocupado por uma pessoa seu status muda
	all T: Taxi, P:Pessoa, t: Time | taxiocupado[T,t,P]
// Taxi só transporta um passageiro por vez
	all T: Taxi, P:Pessoa, P1: Pessoa -P, t: Time | TaxiUmaPessoa[T,t,P,P1]
// todo taxi pego por uma pessoa precisa estar cadastrado
	all p: Pessoa, c: Central | p.taxi in c.cadastrados 
// pessoa só pode ter um taxi por time
	all P: Pessoa, t: Time|  PessoaUmTaxi[P,t]
// taxi pertence a central?
	all T: Taxi, C: Central, t: Time - first | 
		 TaxiPertenceCentral[T,C,t]
// mudança de validade
	all pre: Time - first | let pos = pre.next |
		 all T: Taxi |	mudaValidade[T,pre,pos]
		
	// assert?
	all p: Placa | #(p.~placa) = 1 // botar como assert? o one cobre isso?
	all P: Placa | todoTaxistaComPlaca[P] -- botar como assert
	all T: Taxi, T1: Taxi - T | #(T.placa & T1.placa) = 0 // botar como assert -> Iza
}


--teste
assert testeTaxiPertenceCentral{
	all T: Taxi, C: Central, t,t1: Time - first | 
	T in (C.cadastrados).t <=>  T in (C.cadastrados).t1
}

assert testePessoaUmTaxi{
	all P: Pessoa, t: Time|  # ((P.taxi).t) <= 1
}

assert testeTaxiOcupado {
		all T: Taxi, P:Pessoa, t: Time | (T in (P.taxi).t) implies ((T.status).t = Ocupado) 
}

assert testeTaxiUmaPessoa{
	all T: Taxi, P:Pessoa, P1: Pessoa -P, t: Time | (T in (P.taxi).t) implies (T !in (P1.taxi).t)
}

assert testeTaxiPessoaEmCentral{
	all p: Pessoa, c: Central | p.taxi in c.cadastrados 
}


check testeTaxiPertenceCentral for 6
check testePessoaUmTaxi for 6
check testeTaxiOcupado for 6
check testeTaxiUmaPessoa for 6
check testeTaxiPessoaEmCentral for 6

run init for 6

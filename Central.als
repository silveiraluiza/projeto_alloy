open util/ordering[Time] -- ordenação dos tempos

------------------------------					-- Assinaturas --           -------------------------------------------------

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
	taxi: Taxi -> Time, 
	placapreferida: Placa
}

//------------------ Predicados com manipulção de tempo -------------------------

// Define os status dos taxistas e da central
pred init [t: Time]{
	 Taxi.status.t = Livre  //Um sempre tem status inicial disponível
	no (Central.cadastrados).t   //a central inicia vazia 
}

/////////          TAXI          /////////	
//taxi pode levar apenas um passageiro 
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
pred taxiOcupado[T:Taxi, t:Time, P: Pessoa]{
	(T in (P.taxi).t) implies ((T.status).t = Ocupado) 
}
// muda o status de taxi para livre
pred taxiLivre[T:Taxi, t:Time, P: Pessoa]{
	(T !in (P.taxi).t) implies ((T.status).t = Livre)
}
// em algum ponto do tempo o registro do taxi se tornará inválido
pred mudaValidade[T: Taxi, t0: Time, t1: Time]{
	((T.registro).t0 = Valido) implies (((T.registro).t1 = Valido) or ((T.registro).t1 = Invalido))
}

// Todo taxista possui uma placa identificadora
pred todoTaxistaComPlaca[p1: Placa]{
	p1 in Taxi.placa
}
// Dois taxis são de regiões distintas
pred taxisRegioesDiferentes[t1: Taxi, t2: Taxi - t1]{ -------------------------- AQUI
	 (t1.regiao != t2.regiao)
}

// Um taxi pertence a uma região específica, como norte, ou sul ...
pred taxiDeterminadaRegiao[t: Taxi, r1: Regiao]{	--------------------------------AQUI
	t.regiao = r1
}

//verifica se o taxi está livre
pred taxiEstaLivre[T:Taxi, t:Time, P:Pessoa]{
	T !in (P.taxi).t
}
//verifica se o taxi está ocupado
pred taxiEstaOcupado[T: Taxi,t: Time, P: Pessoa]{
	T in (P.taxi).t
}

pred taxiValido[T: Taxi, t: Time]{
	T in (Central.cadastrados).t
}

pred taxiInvalido[T: Taxi, t: Time]{
	T !in (Central.cadastrados).t
}
/////////////// PESSOA /////////////////////////
// Pessoa sai do Taxi (função)
pred pessoaSaiTaxi[T1: Taxi, t,t': Time, P: Pessoa]{
	(T1 in (P.taxi).t) =>
	 (((P.taxi).t' = (P.taxi).t - T1) || ((P.taxi).t' = (P.taxi).t))
}
// Pessoa chama um taxi (Função)
pred pessoaChamaTaxi[T1: Taxi, t,t': Time, P: Pessoa]{ 
	((P.taxi).t' = ((P.taxi).t + T1)  ) implies (T1 !in (P.taxi).t) && ((T1.regiao = P.r) )	
	
}
//Pessoa chama um taxi pela placa (função)
pred pessoaChamaTaxiPelaPlaca[T1: Taxi, t,t': Time, P: Pessoa]{ 
	((P.taxi).t' = ((P.taxi).t + T1)  ) implies (T1 !in (P.taxi).t) && ((T1.regiao = P.r) && (P.placapreferida = T1.placa) )	
}
pred pessoaUmaPlaca[P:Pessoa]{
	#(P.placapreferida)  < 2
}
//uma pessoa não pode ocupar dois taxis ao mesmo tempo
pred PessoaUmTaxi[P: Pessoa, t: Time]{
	# ((P.taxi).t) < 2
}	

// pessoa chama um taxi com região diferente da sua (função) - Mudou essa!
pred pessoaChamaDifTaxi[T: Taxi, T1: Taxi , t,t': Time, P: Pessoa]{
	taxiEstaOcupado[T,t,P] && taxiEstaLivre[T1,t,P]
	taxisRegioesDiferentes[T,T1]
	(T.regiao = P.r) && (T1.regiao != P.r) && ((T.status).t' = Ocupado || (T.registro).t' = Invalido) 
	(P.taxi).t' = ((P.taxi).t + T1)
	 	 
}
///////////////////////////// CENTRAL /////////////////////////
// adiciona taxi  a central, usaremos? (função)
pred AdcTaxiCentral[T1: Taxi, t,t': Time, C: Central]{
	T1 !in (C.cadastrados).t
	 ((C.cadastrados).t' = (C.cadastrados).t + T1)
}
// Verifica se taxi pertence a central
pred TaxiPertenceCentral[T: Taxi,C: Central,t: Time]{
	  (T !in (C.cadastrados).t) || ((T.registro).t = Valido)
}

/////////////////// REGIÃO ///////////////////////////	
// Todos os taxis que atendem a uma regiao r1, estao com status ocupado
pred regiaoOcupada[t1:Taxi, r1: Regiao, t: Time, P: Pessoa]{ ----------------------------------AQUI
	taxiDeterminadaRegiao[t1, r1]
	taxiEstaOcupado[t1,t,P]
}
pred regiaoUmTaxi[r: Regiao]{
#(r.~regiao) > 0
}
--------------------------------- Facts ----------------------------------------

fact traces{
	init[first]
// Taxista possui apenas  um status (disponivel ou ocupado)
	all T: Taxi, t: Time | taxistaPossuiApenas1Status[T,t]
// Taxista possui apenas um status um registro (válido ou não)
	all T: Taxi, t: Time | taxistaPossuiApenas1Reg[T,t]
// se um taxi estiver ocupado por uma pessoa seu status muda
	all T: Taxi, t: Time, P: Pessoa | taxiOcupado[T,t,P]
// se um taxi não estiver com passageiro ele está livre
	all T: Taxi, t:Time | some P: Pessoa | taxiLivre[T,t,P]
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
		 some T: Taxi |	mudaValidade[T,pre,pos]
// Pessoa chama Taxi
	some pre: Time - first| let pos = pre.next |
		all T: Taxi | all P: Pessoa |
				pessoaChamaTaxi[T,pre,pos,P]

// Pessoa chama Taxi
	some pre: Time - first| let pos = pre.next |
		all T: Taxi | all P: Pessoa |
				pessoaChamaTaxiPelaPlaca[T,pre,pos,P]

//chama taxi de novo
	some pre: Time - first| let pos = pre.next |
		some T: Taxi | all P: Pessoa |
				((P.r = T.regiao) && ( taxiEstaLivre[T,pre,P]) ) => (P.taxi.pos = (P.taxi.pre + T))
// Pessoa sai do Taxi
	some pre: Time - first| let pos = pre.next |
		some T: Taxi, P: Pessoa |
				pessoaSaiTaxi[T,pre,pos,P]
// toda placa possui um taxi
	all p: Placa | #(p.~placa) = 1 
//toda região tem ao menos um taxi
	all r: Regiao | regiaoUmTaxi[r]


}
-------------------------------------------- Asserts -------------------------------------------------------------

assert testeChamaTaxiPelaPlaca{
	some t: Time - first| let t' = t.next |
		all T1: Taxi | all P: Pessoa | ((P.taxi).t' = ((P.taxi).t + T1)  ) implies (T1 !in (P.taxi).t) && ((T1.regiao = P.r) && (P.placapreferida = T1.placa) )	
}

assert testeTaxiPertenceCentral{
	all T: Taxi, C: Central, t: Time - first | 	(T !in (C.cadastrados).t) || ((T.registro).t = Valido)
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

assert testeTodaPlacaDiferente{
	all T: Taxi, T1: Taxi - T | #(T.placa & T1.placa) = 0
}

assert testeTodoTaxistaComPlaca{
	all p1: Placa | p1 in Taxi.placa

}
//Verificar se Taxi cadastrado pode ser inválido (dica, não pode)
assert testeTaxiDaCentralSempreValidos{ 
	all c: Central,T: Invalido, t: Time | #((((c.cadastrados).t).registro).t & T)= 0
}
//Verificar se todo taxi que a pessoa pega é válido (dica, deve)
assert testeTaxiPessoaSempreValido{ 
	all p: Pessoa, v: Valido, t: Time | ((((p.taxi).t).registro).t in v)
}

----------------------------- Run e Checks -----------------------------------------

check testeChamaTaxiPelaPlaca for 6
check testeTaxiDaCentralSempreValidos for 6
check testeTaxiPessoaSempreValido for 6
check testeTaxiPertenceCentral for 6
check testePessoaUmTaxi for 6
check testeTaxiOcupado for 6
check testeTaxiUmaPessoa for 6
check testeTaxiPessoaEmCentral for 6
check  testeTodaPlacaDiferente for 6 -- 
check testeTodoTaxistaComPlaca for 6 --
run init for 6

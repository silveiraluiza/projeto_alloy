module banco

sig Banco{
contas: some Conta
}
sig Conta  {}
sig contaCorrente extends Conta {}
sig Poupanca extends Conta {}
sig contaVip in Conta {}

assert testeBancoSemContas{
all b:Banco | #(b.contas) > 0
}

fact {
all c:Conta | #(c.~contas) > 0
}

check testeBancoSemContas

pred show[]{
}
run show 

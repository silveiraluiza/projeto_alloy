sig Banco{
contas: some Conta
}
sig Conta  {}
sig contaCorrente extends Conta {}
sig Poupanca extends Conta {}
sig contaVip in Conta {}

fact {
all b1, b2 : Banco | no (b1.contas & b2.contas)
all c: Conta | #(c.~contas) = 1
}



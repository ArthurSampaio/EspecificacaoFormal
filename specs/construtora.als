module construtora

//TODOS: Precisa colocar a quantidade de equipes de pedreiro igual a 4

//Entidades
sig Construtora {
	
	predio: one Predio, 
	estadio : one Estadio, 
	condominio : one Condominio,
	engenheiros : one EquipeEngenheiros, 
	pintores : one EquipePintores,
	pedreiros : set EquipePedreiros

}

abstract sig Equipe{
	contratante : one Construtora
}

sig EquipePedreiros in Equipe {}

sig EquipePintores in Equipe {}

sig EquipeEngenheiros in Equipe {

	engCivil: one EngCivil,
	engEletricista: one EngEletricista
}

sig EngCivil {}
sig EngEletricista {}


abstract sig Obra {}

sig Estadio extends Obra{
	construtora : one Construtora,
	fiscal: one FiscalDoEstado
}

sig FiscalDoEstado {
}

sig Predio extends Obra {
	construtora : one Construtora,
	apartamentos: set ApartamentoDePredio
}

sig Condominio extends Obra {
	construtora : one Construtora,
	predios: set PredioDeCondominio
}

sig PredioDeCondominio {
	apartamentos: set ApartamentoDeCondominio
}

sig Proprietario {
}

abstract sig Apartamento {
	proprietario: one Proprietario
}

sig ApartamentoDeCondominio {
	quartos: set Quarto
}

sig ApartamentoDePredio {
	quartos: set Quarto
}

sig Quarto {}


// Fatos

fact todaEquipeEhContratadaPelaConstrutora {

	all E: EquipePedreiros | one c:Construtora | E in pedreirosDaConstrutora[c]
	all p:EquipePintores |  one c:Construtora | p in pintoresDaConstrutora[c]
	all e:EquipeEngenheiros | one c:Construtora | e in engenheirosDaConstrutora[c]
}

fact todaObraEhDaConstrutora {

	all p:Predio | some c:Construtora | p in c.predio
	all e:Estadio | some c:Construtora | e in c.estadio
	all cond:Condominio | some c:Construtora | cond in c.condominio
}


fact ConstrutoraSingleton {
	#Construtora = 1
}

fact QuantidadeDeEquipes {
	all c:Construtora | #engenheirosDaConstrutora[c] = 2 
}

//fact ApartamentoDeCondominioTemUmOuDoisQuartos {
//	all apCond:ApartamentoDeCondominio | #(apCond.quartos) => 1 && #(apCond.quartos) =< 2 
//}


//fact ApartamentoDePredioTemTresQuartos {
	//all apPred:ApartamentoDePredio | #(apPred.quartos) = 3
//}

//fact {
	//all ap:Apartamento | one m.proprietario
	//all p.Proprietario | p.~proprietario
//}

// Functions

fun pedreirosDaConstrutora[c:Construtora]: set EquipePedreiros {
	c.pedreiros
}

fun pintoresDaConstrutora[c:Construtora]: one EquipePintores {
	c.pintores
}

fun engenheirosDaConstrutora[c:Construtora]: one EquipeEngenheiros {
	c.engenheiros
}

pred temPedreiros[c:Construtora]{
	#c.pedreiros = 4
}

// Asserções
assert testeTamanhoDasEquipes {
	all c:Construtora | #(c.pedreiros) = 4
	all c:Construtora | one c.pintores
	all c:Construtora | one c.engenheiros
}

//assert testeTodaObraTemUmaEquipeDePedreiros {
//	all o:Obra | some c:Construtora | #(c.pedreiros) > 0
//}

check testeTamanhoDasEquipes
//check testeTodaObraTemUmaEquipeDePedreiros

// Nao implementados ainda
assert testeEngenheirosTrabalhamSempreJuntos {}

assert testePintoresNaoTrabalhamComEngenheiros {}

assert testeTodoApartamentoTemUmDono {}

assert testeQtdQuartosCondominio {}

assert testeQtdQuartosPredio {}

assert testeTodaEquipeDeEstadioEhAcompanhadaPorFiscal {}

pred show []{}

run show

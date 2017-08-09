module construtora

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

sig EquipePedreiros extends Equipe {}

sig EquipePintores extends Equipe {}

sig EquipeEngenheiros extends Equipe {

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
	apartamento: one Apartamento
}

abstract sig Apartamento {
	proprietario: one Proprietario
}

sig ApartamentoDeCondominio extends Apartamento {
	quartos: set Quarto,
	predio: one PredioDeCondominio
}

sig ApartamentoDePredio extends Apartamento {
	quartos: set Quarto
}

sig Quarto {}

// Facts
fact todaEquipeEhContratadaPelaConstrutora {

	all E: EquipePedreiros | one c:Construtora | E in pedreirosDaConstrutora[c]
	all p:EquipePintores |  one c:Construtora | p in pintoresDaConstrutora[c]
	all e:EquipeEngenheiros | one c:Construtora | e in engenheirosDaConstrutora[c]
}

fact todoApartamentoTemUmProprietario {
	all ap:Apartamento | one ap.proprietario
}

fact umQuartoNaoPodeSerDeApartamentosDiferentes {

}

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

pred show []{}

run show

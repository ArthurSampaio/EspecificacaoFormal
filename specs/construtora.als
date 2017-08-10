module construtora

// Falta Implementar: Cada apartamento tem um dono (no condomínio e no prédio). No condomínio, existem vários prédios, com apartamentos de um e dois quartos.
// Nos prédios, os apartamentos têm todos três quartos. No estádio, cada equipe precisa ser acompanhada por um fiscal do estado; neste caso, cada entrega parcial precisa de ser aprovada.

// Predios do condominio podem ter diferentes quantidadas de quartos?

// Entidades
sig Construtora {
	predio: one Predio,
	condominio: one Condominio,
	estadio: one Estadio
}

abstract sig Obra {
	pedreiros: one EquipeDePedreiros
}

sig Predio extends Obra {
	construtora : one Construtora,
	apartamento3Quartos: set ApartamentoComTresQuartos
}

sig PredioDoCondominio {
	apartamentos1Quarto: set ApartamentoComUmQuarto,
	apartamentos2Quartos: set ApartamentoComDoisQuartos
}

sig Condominio extends Obra {
	construtora : one Construtora,
	predios: set PredioDoCondominio
}

sig Estadio extends Obra {
	construtora : one Construtora
}

sig EquipeDePedreiros {
	obra: lone Obra
}

sig EquipeDePintores {
	obra : one Obra
}

abstract sig Engenheiro {
	obra : one Obra
}

sig EngenheiroEletricista extends Engenheiro {}

sig EngenheiroCivil extends Engenheiro {}

// Dono de algum prédio ou apartamento
sig Pessoa {
	apartamento: some Apartamento
}

// Fiscal do estado; a obra obrigatoriamente deve ter um. Se a obra tem um, então ela é aprovada.
sig Fiscal {}

abstract sig Apartamento {
	pessoa: one Pessoa
}

sig ApartamentoComUmQuarto extends Apartamento {
	predio: one PredioDoCondominio
}

sig ApartamentoComDoisQuartos extends Apartamento {
	predio: one PredioDoCondominio
}

sig ApartamentoComTresQuartos extends Apartamento {
	predio: one Predio
}

// Funções
fun PrediosDoCondominio[c:Condominio]: set PredioDoCondominio {
	c.predios
} 

// Fatos

fact ApartamentoComDonos {
	all p: Pessoa | all apt: Apartamento | apt.pessoa = p => p.apartamento = apt
}

fact quartosDosAptosDoCond {
	all pdc: PredioDoCondominio | all apt: ApartamentoComUmQuarto 
	| (apt in pdc.apartamentos1Quarto) => apt.predio = pdc

	all pdc: PredioDoCondominio | all apt: ApartamentoComDoisQuartos 
	| (apt in pdc.apartamentos2Quartos) => apt.predio = pdc
}

fact ContrutoraUnica {
	#Construtora = 1	
}

fact UmaObraDeCada {
	#Predio = 1
	#Condominio = 1
	#Estadio = 1
}

fact QuantidadeDeFuncionarios {
	#EngenheiroEletricista = 1
	#EngenheiroCivil = 1
	#EquipeDePintores = 1
	all p:EquipeDePedreiros | all o:Obra | o.pedreiros = p => p.obra = o
}

fact EngenheirosUnidos {
	all e:EngenheiroEletricista | all c:EngenheiroCivil | e.obra = c.obra 
}

fact EngenheirosSeparadosDosPintores {
	all e:Engenheiro | all p:EquipeDePintores | e.obra != p.obra
}

pred show []{}

run show

module construtora

// TODOS: Precisa colocar a quantidade de equipes de pedreiro igual a 4

// Entidades
sig Construtora {
	
	predio : one Predio, 
	estadio : one Estadio, 
	condominio : one Condominio
}

 // Uma obra (predio, condominio ou estadio) tem uma construtora.
abstract sig Obra {
		pedreiros : set EquipeDePedreiros
}

sig Predio extends Obra {
	construtora : one Construtora
}
sig Condominio extends Obra {
	construtora : one Construtora
}
sig Estadio extends Obra {
	construtora : one Construtora
}

// Equipes
sig EquipeDePedreiros {
	obra: lone Obra
}

sig EquipeDePintores {
	obra : one Obra
}

// Especialidade do engenheiro, na qual pode ser civil ou eletricista.
abstract sig Especialidade {
	engenheiro : one Engenheiro
}

sig EngenheiroEletricista extends Especialidade {}
sig EngenheiroCivil extends Especialidade {}

abstract sig Engenheiro {
	obra : one Obra,
	especialidade: one Especialidade

}

fact EngenheiroCivilOuEletricista {
	Especialidade = EngenheiroEletricista + EngenheiroCivil
}

fact EngenheiroComEspecialidadeUnica {
	all eng: Engenheiro | some e: Especialidade | eng in e.engenheiro
}

fact FuncionariosPorObra {
	#EngenheiroCivil = 1
	#EngenheiroEletricista = 1
	#EquipeDePintores = 1
	all p: EquipeDePedreiros | all o: Obra | o.pedreiros = p => p.obra = o
}

fact ContrutoraUnica {
	#Construtora = 1	
}

fact UmaObraDeCada {
	#Predio = 1
	#Condominio = 1
	#Estadio = 1
}

fact EngenheirosSeparadosDosPintores {
	all e: Engenheiro | all p: EquipeDePintores | e.obra != p.obra
}

pred show []{}

run show

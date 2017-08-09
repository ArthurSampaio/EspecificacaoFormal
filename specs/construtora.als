module construtora

// TODOS: Precisa colocar a quantidade de equipes de pedreiro igual a 4

// Entidades
sig Construtora {
	
	predio : one Predio, 
	estadio : one Estadio, 
	condominio : one Condominio,
	engenheiros : set Engenheiro, 
	pintores : set Pintor,
	pedreiros : set Pedreiro
}

abstract sig Equipe {
	contratante : one Construtora
}

sig Pedreiro in Equipe {}
sig Pintor in Equipe {}
sig Engenheiro in Equipe {
	especialidade : one Especialidade
}

// Especialidade do engenheiro, na qual pode ser civil ou eletricista.
abstract sig Especialidade {
	engenheiro : one Engenheiro
}

sig Civil extends Especialidade{}
sig Eletricista extends Especialidade{}


abstract sig Obra{} // Uma obra (predio, condominio ou estadio) tem uma construtora.

sig Predio extends Obra {
	construtora : one Construtora
}
sig Condominio extends Obra {
	construtora : one Construtora
}
sig Estadio extends Obra {
	construtora : one Construtora
}

// Fatos
fact EngenheiroCivilOuEletricista {
	Especialidade = Civil + Eletricista
}

fact EngenheiroComEspecialidadeUnica {
	all eng: Engenheiro | some e: Especialidade | eng in e.engenheiro
}

fact todaEquipeEhContratadaPelaConstrutora {
	all E: Pedreiro | some c: Construtora | E in pedreirosDaConstrutora[c]
	all p: Pintor | some c: Construtora | p in pintoresDaConstrutora[c]
	all e: Engenheiro | some c: Construtora | e in engenheirosDaConstrutora[c]

}

fact todaObraEhDaConstrutora {

	all p: Predio | some c: Construtora | p in c.predio
	all e: Estadio | some c: Construtora | e in c.estadio
	all cond: Condominio | some c: Construtora | cond in c.condominio

}

fact ConstrutoraSingleton {
	#Construtora = 1
}

fact QuantidadeDeEquipes {
	all c: Construtora | #(engenheirosDaConstrutora[c]) = 2 && #(pedreirosDaConstrutora[c]) = 4

}



//Funcoes

fun pedreirosDaConstrutora[c:Construtora]: set Pedreiro {
	c.pedreiros
}

fun pintoresDaConstrutora[c:Construtora]: one Pintor {
	c.pintores
}

fun engenheirosDaConstrutora[c:Construtora]: set Engenheiro {
	c.engenheiros
}

--pred temPedreiros[c:Construtora] {
	--#(c.pedreiros) = 4
--}


pred show []{}

run show

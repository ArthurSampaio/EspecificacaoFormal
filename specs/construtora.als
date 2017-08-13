module construtora



//Entidades
sig Construtora {
	predio: one Predio,
	condominio: one Condominio,
	estadio: one Estadio
}

abstract sig Obra{
	pedreiros: one EquipeDePedreiros
}

sig Predio extends Obra{
	construtora : one Construtora,
	apartamentos : set ApartamentoComTresQuartos
}

sig PredioDoCondominio{
	condominio : one Condominio, 
	apartamentos1Quarto: set ApartamentoComUmQuarto,
	apartamentos2Quartos: set ApartamentoComDoisQuartos
}

sig Condominio extends Obra{
	construtora : one Construtora,
	predios: set PredioDoCondominio
}

sig Estadio extends Obra{
	construtora : one Construtora
}


sig EquipeDePedreiros {
	obra: lone Obra
}

one sig EquipeDePintores {
	obra : one Obra
}

abstract sig Engenheiro {
	obra : one Obra
}

one sig EngenheiroEletricista extends Engenheiro {}

one sig EngenheiroCivil extends Engenheiro {}

abstract sig Apartamento{
	dono : one Pessoa
}

sig ApartamentoComUmQuarto extends Apartamento {
	predio: one PredioDoCondominio
	
}

sig ApartamentoComDoisQuartos extends Apartamento {
	predio: one PredioDoCondominio
}


sig ApartamentoComTresQuartos extends Apartamento {
	--Esse tipo de apartamento é apenas para prédios	
	predio : one Predio

}

sig Pessoa{
	apartamentos : some Apartamento
}

//Funções



fun PrediosDoCondominio[c:Condominio]: set PredioDoCondominio {
	c.predios
} 


//Fatos

fact PredioDoCondominioPossuiQuartos {
	all p:PredioDoCondominio | QuantidadeDeQuartos[p]
}

fact TodoPredioDeCondominioTemUmCondominio {

	all p:PredioDoCondominio | some c:Condominio | PredioEstaNoCondominio[p,c]
}

fact QuantidadeDePrediosPorCondominio {
	all c: Condominio| #c.predios = 2	
}

fact TodaPessoaTemPeloMenosUmApartamento {
	all p:Pessoa | temApartamentos[p]
	all ap:Apartamento | all p:Pessoa | apartamentoTemDonoUnico[ap,p]
}

fact quartosDosAptosDoCond {
	all pdc:PredioDoCondominio | all apt:ApartamentoComUmQuarto 
	| (apt in pdc.apartamentos1Quarto) => apt.predio = pdc

	all pdc:PredioDoCondominio | all apt:ApartamentoComDoisQuartos 
	| (apt in pdc.apartamentos2Quartos) => apt.predio = pdc
}


fact PedreirosTrabalhamEmApenasUmObraPorVez {
	all p:EquipeDePedreiros | all o:Obra | pedreirosEmUmaUnicaObra[p,o]
}

fact EngenheirosUnidos {
	all e:EngenheiroEletricista | all c:EngenheiroCivil | e.obra = c.obra 
}

fact EngenheirosSeparadosDosPintores {
	all e:Engenheiro | all p:EquipeDePintores | engenheiroNaoTrabalhaComPintores[e,p]
}

//Predicados

pred QuantidadeDeQuartos[p:PredioDoCondominio]{

	#p.apartamentos1Quarto = 2 <=> #p.apartamentos2Quartos = 2

}

pred PredioEstaNoCondominio[p:PredioDoCondominio, c:Condominio]{
	 p.condominio = c <=> p in c.predios
}

pred temApartamentos[p:Pessoa]{
	some p.apartamentos
}

pred pedreirosEmUmaUnicaObra[p:EquipeDePedreiros, o:Obra]{
	 o.pedreiros = p => p.obra = o
}

pred engenheiroNaoTrabalhaComPintores[e:Engenheiro, p:EquipeDePintores]{
	 e.obra != p.obra
}

pred apartamentoTemDonoUnico[ap:Apartamento, p:Pessoa]{
	ap.dono = p <=> ap in p.apartamentos
}

pred show []{
	#Construtora = 1	
}



run show for 3 but 8 Apartamento


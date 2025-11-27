:- dynamic parserVersionNum/1, parserVersionStr/1, parseResult/5.
:- dynamic module/4.
'parserVersionStr'('0.6.2.1').
'parseResult'('ok','',0,0,0).
:- dynamic channel/2, bindval/3, agent/3.
:- dynamic agent_curry/3, symbol/4.
:- dynamic dataTypeDef/2, subTypeDef/2, nameType/2.
:- dynamic cspTransparent/1.
:- dynamic cspPrint/1.
:- dynamic pragma/1.
:- dynamic comment/2.
:- dynamic assertBool/1, assertRef/5, assertTauPrio/6.
:- dynamic assertModelCheckExt/4, assertModelCheck/3.
:- dynamic assertLtl/4, assertCtl/4.
'parserVersionNum'([0,11,1,1]).
'parserVersionStr'('CSPM-Frontent-0.11.1.1').
'bindval'('nbClient','int'(2),'src_span'(1,1,1,13,0,12)).
'bindval'('nbServeur','int'(2),'src_span'(2,1,2,14,13,13)).
'bindval'('CLIENT','setExp'('rangeClosed'('int'(1),'val_of'('nbClient','src_span'(4,14,4,22,41,8)))),'src_span'(4,1,4,23,28,22)).
'bindval'('SERVEUR','setExp'('rangeClosed'('int'(1),'val_of'('nbServeur','src_span'(5,15,5,24,65,9)))),'src_span'(5,1,5,25,51,24)).
'channel'('CaR','type'('dotTupleType'(['val_of'('CLIENT','src_span'(7,15,7,21,91,6))]))).
'channel'('RaS','type'('dotTupleType'(['val_of'('CLIENT','src_span'(8,15,8,21,112,6)),'val_of'('SERVEUR','src_span'(8,22,8,29,119,7))]))).
'channel'('SaR','type'('dotTupleType'(['val_of'('CLIENT','src_span'(9,15,9,21,141,6)),'val_of'('SERVEUR','src_span'(9,22,9,29,148,7))]))).
'channel'('RaC','type'('dotTupleType'(['val_of'('CLIENT','src_span'(10,15,10,21,170,6))]))).
'bindval'('CR','closure'(['CaR','RaC']),'src_span'(12,1,12,20,178,19)).
'bindval'('RS','closure'(['RaS','SaR']),'src_span'(13,1,13,20,198,19)).
'agent'('Client'(_i),'prefix'('src_span'(15,13,15,16,231,3),['out'(_i)],'CaR','prefix'('src_span'(15,22,15,25,240,3),['out'(_i)],'RaC','agent_call'('src_span'(15,31,15,37,249,6),'Client',[_i]),'src_span'(15,28,15,30,245,15)),'src_span'(15,19,15,21,236,24)),'src_span'(15,13,15,40,231,27)).
'bindval'('Repartiteur','|||'('val_of'('RequeteClient','src_span'(17,16,17,29,275,13)),'val_of'('ReponseServeur','src_span'(17,34,17,48,293,14)),'src_span_operator'('no_loc_info_available','src_span'(17,30,17,33,289,3))),'src_span'(17,1,17,48,260,47)).
'bindval'('RequeteClient','prefix'('src_span'(19,17,19,20,325,3),['inGuard'(_i2,'val_of'('CLIENT','src_span'(19,23,19,29,331,6)))],'CaR','prefix'('src_span'(19,33,19,36,341,3),['out'(_i2),'inGuard'(_j,'val_of'('SERVEUR','src_span'(19,41,19,48,349,7)))],'RaS','val_of'('RequeteClient','src_span'(19,52,19,65,360,13)),'src_span'(19,49,19,51,356,27)),'src_span'(19,30,19,32,337,45)),'src_span'(19,1,19,65,309,64)).
'bindval'('ReponseServeur','prefix'('src_span'(21,18,21,21,392,3),['inGuard'(_i3,'val_of'('CLIENT','src_span'(21,24,21,30,398,6))),'inGuard'(_j2,'val_of'('SERVEUR','src_span'(21,33,21,40,407,7)))],'SaR','prefix'('src_span'(21,44,21,47,418,3),['out'(_i3)],'RaC','val_of'('ReponseServeur','src_span'(21,53,21,67,427,14)),'src_span'(21,50,21,52,423,20)),'src_span'(21,41,21,43,414,37)),'src_span'(21,1,21,67,375,66)).
'agent'('Serveur'(_j3),'prefix'('src_span'(23,14,23,17,456,3),['inGuard'(_i4,'val_of'('CLIENT','src_span'(23,20,23,26,462,6))),'out'(_j3)],'RaS','prefix'('src_span'(23,32,23,35,474,3),['out'(_i4),'out'(_j3)],'SaR','agent_call'('src_span'(23,43,23,50,485,7),'Serveur',[_j3]),'src_span'(23,40,23,42,481,16)),'src_span'(23,29,23,31,470,27)),'src_span'(23,14,23,53,456,39)).
'bindval'('MAIN','sharing'('val_of'('RS','src_span'(31,4,31,6,597,2)),'sharing'('val_of'('CR','src_span'(28,8,28,10,554,2)),'repInterleave'(['comprehensionGenerator'(_i5,'val_of'('CLIENT','src_span'(27,18,27,24,527,6)))],'agent_call'('src_span'(27,27,27,33,536,6),'Client',[_i5]),'src_span'(27,14,27,26,523,12)),'val_of'('Repartiteur','src_span'(29,9,29,20,568,11)),'src_span'(28,5,28,13,551,8)),'repInterleave'(['comprehensionGenerator'(_j4,'val_of'('SERVEUR','src_span'(32,14,32,21,616,7)))],'agent_call'('src_span'(32,24,32,31,626,7),'Serveur',[_j4]),'src_span'(32,10,32,23,612,13)),'src_span'(31,1,31,9,594,8)),'src_span'(25,1,32,35,497,140)).
'assertModelCheckExt'('False','val_of'('MAIN','src_span'(42,8,42,12,882,4)),'DeadlockFree','F').
'comment'('blockComment'('{-\xa\assert MAIN |= LTL: "G ([CaR.1] => F ([RaS.1.1] or [RaS.1.2]))"\xa\assert MAIN |= LTL: "G ([CaR.1] => F [RaC.1])"\xa\assert MAIN |= LTL: "G ([CaR.2] => F [RaC.2])"\xa\assert MAIN |= LTL: "GF ([CaR.1])"\xa\assert MAIN |= LTL: "GF (e(CaR.1))"\xa\-}'),'src_position'(34,1,639,234)).
'symbol'('nbClient','nbClient','src_span'(1,1,1,9,0,8),'Ident (Groundrep.)').
'symbol'('nbServeur','nbServeur','src_span'(2,1,2,10,13,9),'Ident (Groundrep.)').
'symbol'('CLIENT','CLIENT','src_span'(4,1,4,7,28,6),'Ident (Groundrep.)').
'symbol'('SERVEUR','SERVEUR','src_span'(5,1,5,8,51,7),'Ident (Groundrep.)').
'symbol'('CaR','CaR','src_span'(7,9,7,12,85,3),'Channel').
'symbol'('RaS','RaS','src_span'(8,9,8,12,106,3),'Channel').
'symbol'('SaR','SaR','src_span'(9,9,9,12,135,3),'Channel').
'symbol'('RaC','RaC','src_span'(10,9,10,12,164,3),'Channel').
'symbol'('CR','CR','src_span'(12,1,12,3,178,2),'Ident (Groundrep.)').
'symbol'('RS','RS','src_span'(13,1,13,3,198,2),'Ident (Groundrep.)').
'symbol'('Client','Client','src_span'(15,1,15,7,219,6),'Funktion or Process').
'symbol'('i','i','src_span'(15,8,15,9,226,1),'Ident (Prolog Variable)').
'symbol'('Repartiteur','Repartiteur','src_span'(17,1,17,12,260,11),'Ident (Groundrep.)').
'symbol'('RequeteClient','RequeteClient','src_span'(19,1,19,14,309,13),'Ident (Groundrep.)').
'symbol'('i2','i','src_span'(19,21,19,22,329,1),'Ident (Prolog Variable)').
'symbol'('j','j','src_span'(19,39,19,40,347,1),'Ident (Prolog Variable)').
'symbol'('ReponseServeur','ReponseServeur','src_span'(21,1,21,15,375,14),'Ident (Groundrep.)').
'symbol'('i3','i','src_span'(21,22,21,23,396,1),'Ident (Prolog Variable)').
'symbol'('j2','j','src_span'(21,31,21,32,405,1),'Ident (Prolog Variable)').
'symbol'('Serveur','Serveur','src_span'(23,1,23,8,443,7),'Funktion or Process').
'symbol'('j3','j','src_span'(23,9,23,10,451,1),'Ident (Prolog Variable)').
'symbol'('i4','i','src_span'(23,18,23,19,460,1),'Ident (Prolog Variable)').
'symbol'('MAIN','MAIN','src_span'(25,1,25,5,497,4),'Ident (Groundrep.)').
'symbol'('i5','i','src_span'(27,14,27,15,523,1),'Ident (Prolog Variable)').
'symbol'('j4','j','src_span'(32,10,32,11,612,1),'Ident (Prolog Variable)').
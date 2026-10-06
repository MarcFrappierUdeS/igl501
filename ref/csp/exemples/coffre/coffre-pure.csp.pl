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
'bindval'('nbCoffre','int'(1),'src_span'(1,1,1,13,0,12)).
'bindval'('clebanque','int'(0),'src_span'(2,1,2,14,13,13)).
'bindval'('COFFRE','setExp'('rangeClosed'('int'(1),'val_of'('nbCoffre','src_span'(3,14,3,22,40,8)))),'src_span'(3,1,3,23,27,22)).
'bindval'('CLE','agent_call'('src_span'(4,7,4,12,56,5),'union',['val_of'('COFFRE','src_span'(4,13,4,19,62,6)),'setExp'('rangeEnum'(['val_of'('clebanque','src_span'(4,21,4,30,70,9))]))]),'src_span'(4,1,4,32,50,31)).
'channel'('inserer','type'('dotTupleType'(['val_of'('COFFRE','src_span'(6,28,6,34,110,6)),'val_of'('CLE','src_span'(6,37,6,40,119,3))]))).
'channel'('enlever','type'('dotTupleType'(['val_of'('COFFRE','src_span'(6,28,6,34,110,6)),'val_of'('CLE','src_span'(6,37,6,40,119,3))]))).
'channel'('ouvrir','type'('dotTupleType'(['val_of'('COFFRE','src_span'(7,27,7,33,149,6))]))).
'channel'('fermer','type'('dotTupleType'(['val_of'('COFFRE','src_span'(7,27,7,33,149,6))]))).
'bindval'('CLEACT','closure'(['inserer','enlever']),'src_span'(9,1,9,32,157,31)).
'bindval'('PORTEACT','closure'(['ouvrir','fermer']),'src_span'(10,1,10,32,189,31)).
'agent'('Cle'(_k),'prefix'('src_span'(13,5,13,12,235,7),['inGuard'(_c,'val_of'('COFFRE','src_span'(13,15,13,21,245,6))),'out'(_k)],'inserer','agent_call'('src_span'(13,27,13,37,257,10),'CleInseree',[_c,_k]),'src_span'(13,24,13,26,253,21)),'src_span'(13,5,13,42,235,37)).
'agent'('CleInseree'(_c2,_k2),'[]'('&'('bool_or'('=='(_k2,'val_of'('clebanque','src_span'(16,15,16,24,307,9))),'=='(_k2,_c2)),'prefix'('src_span'(16,35,16,41,327,6),['out'(_c2)],'ouvrir','agent_call'('src_span'(16,47,16,57,339,10),'CleInseree',[_c2,_k2]),'src_span'(16,44,16,46,335,21))),'prefix'('src_span'(18,9,18,16,371,7),['out'(_c2),'out'(_k2)],'enlever','agent_call'('src_span'(18,24,18,27,386,3),'Cle',[_k2]),'src_span'(18,21,18,23,382,12)),'src_span_operator'('no_loc_info_available','src_span'(17,5,17,7,360,2))),'no_loc_info_available').
'agent'('Coffre'(_c3),'|||'('agent_call'('src_span'(20,13,20,20,406,7),'Serrure',[_c3]),'agent_call'('src_span'(20,28,20,35,421,7),'Serrure',[_c3]),'src_span_operator'('no_loc_info_available','src_span'(20,24,20,27,417,3))),'no_loc_info_available').
'agent'('Serrure'(_c4),'prefix'('src_span'(23,5,23,12,451,7),['out'(_c4),'inGuard'(_k3,'val_of'('CLE','src_span'(23,17,23,20,463,3)))],'inserer','prefix'('src_span'(23,24,23,31,470,7),['out'(_c4),'out'(_k3)],'enlever','agent_call'('src_span'(23,39,23,46,485,7),'Serrure',[_c4]),'src_span'(23,36,23,38,481,16)),'src_span'(23,21,23,23,466,35)),'src_span'(23,5,23,49,451,44)).
'agent'('Porte'(_c5),'prefix'('src_span'(25,12,25,18,508,6),['out'(_c5)],'ouvrir','prefix'('src_span'(25,24,25,30,520,6),['out'(_c5)],'fermer','agent_call'('src_span'(25,36,25,41,532,5),'Porte',[_c5]),'src_span'(25,33,25,35,528,14)),'src_span'(25,21,25,23,516,26)),'src_span'(25,12,25,44,508,32)).
'bindval'('MAIN','sharing'('closure'(['ouvrir']),'sharing'('val_of'('CLEACT','src_span'(33,8,33,14,672,6)),'sharing'('closure'(['ouvrir']),'repInterleave'(['comprehensionGenerator'(_k4,'val_of'('COFFRE','src_span'(29,22,29,28,582,6)))],'agent_call'('src_span'(29,31,29,34,591,3),'Cle',[_k4]),'src_span'(29,18,29,30,578,12)),'agent_call'('src_span'(31,13,31,16,639,3),'Cle',['int'(0)]),'src_span'(30,10,30,28,608,18)),'repInterleave'(['comprehensionGenerator'(_c6,'val_of'('COFFRE','src_span'(34,19,34,25,700,6)))],'agent_call'('src_span'(34,28,34,34,709,6),'Coffre',[_c6]),'src_span'(34,15,34,27,696,12)),'src_span'(33,5,33,17,669,12)),'repInterleave'(['comprehensionGenerator'(_c7,'val_of'('COFFRE','src_span'(37,15,37,21,760,6)))],'agent_call'('src_span'(37,24,37,29,769,5),'Porte',[_c7]),'src_span'(37,11,37,23,756,12)),'src_span'(36,1,36,19,727,18)),'src_span'(27,1,37,34,542,237)).
'bindval'('PropBankKeyIn','agent_call'('src_span'(39,18,39,21,798,3),'Cle',['int'(0)]),'src_span'(39,1,39,24,781,23)).
'nameType'('INSERER','type'('dotTupleType'(['setExp'('rangeEnum'(['inserer'])),'val_of'('COFFRE','src_span'(41,30,41,36,835,6)),'val_of'('COFFRE','src_span'(41,37,41,43,842,6))]))).
'nameType'('ENLEVER','type'('dotTupleType'(['setExp'('rangeEnum'(['enlever'])),'val_of'('COFFRE','src_span'(42,30,42,36,878,6)),'val_of'('COFFRE','src_span'(42,37,42,43,885,6))]))).
'nameType'('FERMER','type'('dotTupleType'(['setExp'('rangeEnum'(['fermer'])),'val_of'('COFFRE','src_span'(43,28,43,34,919,6))]))).
'assertRef'('False','val_of'('PropBankKeyIn','src_span'(45,8,45,21,934,13)),'Trace','\x5c\'('val_of'('MAIN','src_span'(45,28,45,32,954,4)),'agent_call'('src_span'(45,35,45,40,961,5),'union',['FERMER','agent_call'('src_span'(45,48,45,53,974,5),'union',['INSERER','ENLEVER'])]),'src_span_operator'('no_loc_info_available','src_span'(45,33,45,34,959,1))),'src_span'(45,1,45,72,927,71)).
'symbol'('nbCoffre','nbCoffre','src_span'(1,1,1,9,0,8),'Ident (Groundrep.)').
'symbol'('clebanque','clebanque','src_span'(2,1,2,10,13,9),'Ident (Groundrep.)').
'symbol'('COFFRE','COFFRE','src_span'(3,1,3,7,27,6),'Ident (Groundrep.)').
'symbol'('CLE','CLE','src_span'(4,1,4,4,50,3),'Ident (Groundrep.)').
'symbol'('union','union','src_span'(4,7,4,12,56,5),'BuiltIn primitive').
'symbol'('inserer','inserer','src_span'(6,9,6,16,91,7),'Channel').
'symbol'('enlever','enlever','src_span'(6,18,6,25,100,7),'Channel').
'symbol'('ouvrir','ouvrir','src_span'(7,9,7,15,131,6),'Channel').
'symbol'('fermer','fermer','src_span'(7,17,7,23,139,6),'Channel').
'symbol'('CLEACT','CLEACT','src_span'(9,1,9,7,157,6),'Ident (Groundrep.)').
'symbol'('PORTEACT','PORTEACT','src_span'(10,1,10,9,189,8),'Ident (Groundrep.)').
'symbol'('Cle','Cle','src_span'(12,1,12,4,222,3),'Funktion or Process').
'symbol'('k','k','src_span'(12,5,12,6,226,1),'Ident (Prolog Variable)').
'symbol'('c','c','src_span'(13,13,13,14,243,1),'Ident (Prolog Variable)').
'symbol'('CleInseree','CleInseree','src_span'(15,1,15,11,274,10),'Funktion or Process').
'symbol'('c2','c','src_span'(15,12,15,13,285,1),'Ident (Prolog Variable)').
'symbol'('k2','k','src_span'(15,14,15,15,287,1),'Ident (Prolog Variable)').
'symbol'('Coffre','Coffre','src_span'(20,1,20,7,394,6),'Funktion or Process').
'symbol'('c3','c','src_span'(20,8,20,9,401,1),'Ident (Prolog Variable)').
'symbol'('Serrure','Serrure','src_span'(22,1,22,8,433,7),'Funktion or Process').
'symbol'('c4','c','src_span'(22,9,22,10,441,1),'Ident (Prolog Variable)').
'symbol'('k3','k','src_span'(23,15,23,16,461,1),'Ident (Prolog Variable)').
'symbol'('Porte','Porte','src_span'(25,1,25,6,497,5),'Funktion or Process').
'symbol'('c5','c','src_span'(25,7,25,8,503,1),'Ident (Prolog Variable)').
'symbol'('MAIN','MAIN','src_span'(27,1,27,5,542,4),'Ident (Groundrep.)').
'symbol'('k4','k','src_span'(29,18,29,19,578,1),'Ident (Prolog Variable)').
'symbol'('c6','c','src_span'(34,15,34,16,696,1),'Ident (Prolog Variable)').
'symbol'('c7','c','src_span'(37,11,37,12,756,1),'Ident (Prolog Variable)').
'symbol'('PropBankKeyIn','PropBankKeyIn','src_span'(39,1,39,14,781,13),'Ident (Groundrep.)').
'symbol'('INSERER','INSERER','src_span'(41,10,41,17,815,7),'Nametype').
'symbol'('ENLEVER','ENLEVER','src_span'(42,10,42,17,858,7),'Nametype').
'symbol'('FERMER','FERMER','src_span'(43,10,43,16,901,6),'Nametype').
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
'bindval'('SV_CLEACT','closure'(['inserer','enlever']),'src_span'(9,1,9,35,157,34)).
'bindval'('SV_PORTEACT','closure'(['ouvrir']),'src_span'(10,1,10,27,192,26)).
'agent'('SV_Cle'(_k),'prefix'('src_span'(13,5,13,12,236,7),['inGuard'(_c,'val_of'('COFFRE','src_span'(13,15,13,21,246,6))),'out'(_k)],'inserer','prefix'('src_span'(13,27,13,34,258,7),['out'(_c),'out'(_k)],'enlever','agent_call'('src_span'(13,42,13,48,273,6),'SV_Cle',[_k]),'src_span'(13,39,13,41,269,15)),'src_span'(13,24,13,26,254,30)),'src_span'(13,5,13,51,236,46)).
'agent'('SV_Coffre'(_c2),'|||'('agent_call'('src_span'(15,16,15,26,299,10),'SV_Serrure',[_c2]),'agent_call'('src_span'(15,34,15,44,317,10),'SV_Serrure',[_c2]),'src_span_operator'('no_loc_info_available','src_span'(15,30,15,33,313,3))),'no_loc_info_available').
'agent'('SV_Serrure'(_c3),'prefix'('src_span'(18,5,18,12,353,7),['out'(_c3),'inGuard'(_k2,'val_of'('CLE','src_span'(18,17,18,20,365,3)))],'inserer','prefix'('src_span'(18,24,18,31,372,7),['out'(_c3),'out'(_k2)],'enlever','agent_call'('src_span'(18,39,18,49,387,10),'SV_Serrure',[_c3]),'src_span'(18,36,18,38,383,19)),'src_span'(18,21,18,23,368,38)),'src_span'(18,5,18,52,353,47)).
'agent'('SV_Porte'(_c4),'prefix'('src_span'(20,15,20,21,416,6),['out'(_c4)],'ouvrir','prefix'('src_span'(20,27,20,33,428,6),['out'(_c4)],'fermer','agent_call'('src_span'(20,39,20,47,440,8),'SV_Porte',[_c4]),'src_span'(20,36,20,38,436,17)),'src_span'(20,24,20,26,424,29)),'src_span'(20,15,20,50,416,35)).
'agent'('SV_PorteCTRL'(_c5,_s),'[]'('[]'('&'('=='(_s,'setExp'('rangeEnum'(['val_of'('clebanque','src_span'(23,10,23,19,483,9)),_c5]))),'prefix'('src_span'(23,25,23,31,498,6),['out'(_c5)],'ouvrir','agent_call'('src_span'(23,37,23,49,510,12),'SV_PorteCTRL',[_c5,_s]),'src_span'(23,34,23,36,506,23))),'prefix'('src_span'(24,6,24,13,534,7),['out'(_c5),'inGuard'(_k3,'val_of'('CLE','src_span'(24,18,24,21,546,3)))],'inserer','agent_call'('src_span'(24,25,24,37,553,12),'SV_PorteCTRL',[_c5,'agent_call'('src_span'(24,40,24,45,568,5),'union',[_s,'setExp'('rangeEnum'([_k3]))])]),'src_span'(24,22,24,24,549,38)),'src_span_operator'('no_loc_info_available','src_span'(24,1,24,3,529,2))),'prefix'('src_span'(25,6,25,13,588,7),['out'(_c5),'inGuard'(_k4,'val_of'('CLE','src_span'(25,18,25,21,600,3)))],'enlever','agent_call'('src_span'(25,25,25,37,607,12),'SV_PorteCTRL',[_c5,'agent_call'('src_span'(25,40,25,44,622,4),'diff',[_s,'setExp'('rangeEnum'([_k4]))])]),'src_span'(25,22,25,24,603,37)),'src_span_operator'('no_loc_info_available','src_span'(25,1,25,3,583,2))),'no_loc_info_available').
'bindval'('SV_MAIN','sharing'('val_of'('SV_CLEACT','src_span'(32,4,32,13,754,9)),'sharing'('val_of'('SV_CLEACT','src_span'(29,12,29,21,692,9)),'repInterleave'(['comprehensionGenerator'(_k5,'val_of'('CLE','src_span'(28,17,28,20,663,3)))],'agent_call'('src_span'(28,23,28,29,669,6),'SV_Cle',[_k5]),'src_span'(28,13,28,22,659,9)),'repInterleave'(['comprehensionGenerator'(_c6,'val_of'('COFFRE','src_span'(30,17,30,23,721,6)))],'agent_call'('src_span'(30,26,30,35,730,9),'SV_Coffre',[_c6]),'src_span'(30,13,30,25,717,12)),'src_span'(29,9,29,24,689,15)),'sharing'('val_of'('SV_PORTEACT','src_span'(34,12,34,23,817,11)),'repInterleave'(['comprehensionGenerator'(_c7,'val_of'('COFFRE','src_span'(33,17,33,23,783,6)))],'agent_call'('src_span'(33,26,33,34,792,8),'SV_Porte',[_c7]),'src_span'(33,13,33,25,779,12)),'repInterleave'(['comprehensionGenerator'(_c8,'val_of'('COFFRE','src_span'(35,17,35,23,848,6)))],'agent_call'('src_span'(35,26,35,38,857,12),'SV_PorteCTRL',[_c8,'setExp'('rangeEnum'([]))]),'src_span'(35,13,35,25,844,12)),'src_span'(34,9,34,26,814,17)),'src_span'(32,1,32,16,751,15)),'src_span'(27,1,36,6,637,246)).
'symbol'('nbCoffre','nbCoffre','src_span'(1,1,1,9,0,8),'Ident (Groundrep.)').
'symbol'('clebanque','clebanque','src_span'(2,1,2,10,13,9),'Ident (Groundrep.)').
'symbol'('COFFRE','COFFRE','src_span'(3,1,3,7,27,6),'Ident (Groundrep.)').
'symbol'('CLE','CLE','src_span'(4,1,4,4,50,3),'Ident (Groundrep.)').
'symbol'('union','union','src_span'(4,7,4,12,56,5),'BuiltIn primitive').
'symbol'('inserer','inserer','src_span'(6,9,6,16,91,7),'Channel').
'symbol'('enlever','enlever','src_span'(6,18,6,25,100,7),'Channel').
'symbol'('ouvrir','ouvrir','src_span'(7,9,7,15,131,6),'Channel').
'symbol'('fermer','fermer','src_span'(7,17,7,23,139,6),'Channel').
'symbol'('SV_CLEACT','SV_CLEACT','src_span'(9,1,9,10,157,9),'Ident (Groundrep.)').
'symbol'('SV_PORTEACT','SV_PORTEACT','src_span'(10,1,10,12,192,11),'Ident (Groundrep.)').
'symbol'('SV_Cle','SV_Cle','src_span'(12,1,12,7,220,6),'Funktion or Process').
'symbol'('k','k','src_span'(12,8,12,9,227,1),'Ident (Prolog Variable)').
'symbol'('c','c','src_span'(13,13,13,14,244,1),'Ident (Prolog Variable)').
'symbol'('SV_Coffre','SV_Coffre','src_span'(15,1,15,10,284,9),'Funktion or Process').
'symbol'('c2','c','src_span'(15,11,15,12,294,1),'Ident (Prolog Variable)').
'symbol'('SV_Serrure','SV_Serrure','src_span'(17,1,17,11,332,10),'Funktion or Process').
'symbol'('c3','c','src_span'(17,12,17,13,343,1),'Ident (Prolog Variable)').
'symbol'('k2','k','src_span'(18,15,18,16,363,1),'Ident (Prolog Variable)').
'symbol'('SV_Porte','SV_Porte','src_span'(20,1,20,9,402,8),'Funktion or Process').
'symbol'('c4','c','src_span'(20,10,20,11,411,1),'Ident (Prolog Variable)').
'symbol'('SV_PorteCTRL','SV_PorteCTRL','src_span'(22,1,22,13,453,12),'Funktion or Process').
'symbol'('c5','c','src_span'(22,14,22,15,466,1),'Ident (Prolog Variable)').
'symbol'('s','s','src_span'(22,16,22,17,468,1),'Ident (Prolog Variable)').
'symbol'('k3','k','src_span'(24,16,24,17,544,1),'Ident (Prolog Variable)').
'symbol'('k4','k','src_span'(25,16,25,17,598,1),'Ident (Prolog Variable)').
'symbol'('diff','diff','src_span'(25,40,25,44,622,4),'BuiltIn primitive').
'symbol'('SV_MAIN','SV_MAIN','src_span'(27,1,27,8,637,7),'Ident (Groundrep.)').
'symbol'('k5','k','src_span'(28,13,28,14,659,1),'Ident (Prolog Variable)').
'symbol'('c6','c','src_span'(30,13,30,14,717,1),'Ident (Prolog Variable)').
'symbol'('c7','c','src_span'(33,13,33,14,779,1),'Ident (Prolog Variable)').
'symbol'('c8','c','src_span'(35,13,35,14,844,1),'Ident (Prolog Variable)').
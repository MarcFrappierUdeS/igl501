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
'agent'('removex'(_l,_x),'ifte'('=='(_l,'listExp'('rangeEnum'([]))),'listExp'('rangeEnum'([])),'ifte'('=='(_x,'agent_call'('src_span'(7,19,7,23,123,4),'head',[_l])),'agent_call'('src_span'(8,12,8,16,144,4),'tail',[_l]),'^'('listExp'('rangeEnum'(['agent_call'('src_span'(10,8,10,12,170,4),'head',[_l])])),'agent_call'('src_span'(10,17,10,24,179,7),'removex',['agent_call'('src_span'(10,25,10,29,187,4),'tail',[_l]),_x])),'src_span'(7,10,7,27,114,17),'src_span'(7,28,8,11,131,34),'no_loc_info_available'),'src_span'(5,5,5,17,76,12),'src_span'(5,18,6,11,88,24),'src_span'(6,15,7,9,103,96)),'src_span'(5,5,10,35,76,121)).
'bindval'('nbTel','int'(4),'src_span'(17,1,17,10,403,9)).
'bindval'('TELEPHONE','setExp'('rangeClosed'('int'(1),'val_of'('nbTel','src_span'(18,17,18,22,429,5)))),'src_span'(18,1,18,23,413,22)).
'channel'('dec','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(21,32,21,41,503,9))]))).
'channel'('rac','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(21,32,21,41,503,9))]))).
'channel'('ton','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(21,32,21,41,503,9))]))).
'channel'('tonOc','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(21,32,21,41,503,9))]))).
'channel'('comp','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(22,44,22,53,556,9)),'val_of'('TELEPHONE','src_span'(22,54,22,63,566,9))]))).
'channel'('debSon','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(22,44,22,53,556,9)),'val_of'('TELEPHONE','src_span'(22,54,22,63,566,9))]))).
'channel'('finSon','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(22,44,22,53,556,9)),'val_of'('TELEPHONE','src_span'(22,54,22,63,566,9))]))).
'channel'('conn','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(22,44,22,53,556,9)),'val_of'('TELEPHONE','src_span'(22,54,22,63,566,9))]))).
'channel'('decon','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(22,44,22,53,556,9)),'val_of'('TELEPHONE','src_span'(22,54,22,63,566,9))]))).
'channel'('acq','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(25,27,25,36,688,9))]))).
'channel'('lib','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(25,27,25,36,688,9))]))).
'channel'('estDec','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(25,27,25,36,688,9))]))).
'channel'('estOc','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(26,25,26,34,730,9)),'val_of'('TELEPHONE','src_span'(26,35,26,44,740,9))]))).
'channel'('acqPar','type'('dotTupleType'(['val_of'('TELEPHONE','src_span'(26,25,26,34,730,9)),'val_of'('TELEPHONE','src_span'(26,35,26,44,740,9))]))).
'bindval'('SYNC','closure'(['dec','rac','comp']),'src_span'(28,1,28,28,751,27)).
'bindval'('CTRL','closure'(['acq','acqPar','lib','estOc','estDec']),'src_span'(29,1,29,45,779,44)).
'bindval'('Main','sharing'('agent_call'('src_span'(31,23,31,28,847,5),'union',['val_of'('SYNC','src_span'(31,29,31,33,853,4)),'val_of'('CTRL','src_span'(31,34,31,38,858,4))]),'val_of'('tousAppels','src_span'(31,9,31,19,833,10)),'val_of'('controleTousAppels','src_span'(31,43,31,61,867,18)),'src_span'(31,20,31,42,844,22)),'src_span'(31,1,31,62,825,61)).
'bindval'('MainEnv','\x5c\'('val_of'('Main','src_span'(33,11,33,15,898,4)),'val_of'('CTRL','src_span'(33,18,33,22,905,4)),'src_span_operator'('no_loc_info_available','src_span'(33,16,33,17,903,1))),'src_span'(33,1,33,22,888,21)).
'bindval'('tousAppels','repInterleave'(['comprehensionGenerator'(_n,'val_of'('TELEPHONE','src_span'(35,22,35,31,932,9)))],'agent_call'('src_span'(35,34,35,39,944,5),'appel',[_n]),'src_span'(35,18,35,33,928,15)),'src_span'(35,1,35,42,911,41)).
'bindval'('controleTousAppels','repInterleave'(['comprehensionGenerator'(_n2,'val_of'('TELEPHONE','src_span'(37,30,37,39,983,9)))],'agent_call'('src_span'(37,42,37,55,995,13),'controleAppel',[_n2,'true','listExp'('rangeEnum'([])),'false']),'src_span'(37,26,37,41,979,15)),'src_span'(37,1,37,75,954,74)).
'agent'('controleAppel'(_n1,_libre,_f,_aDec),'[]'('[]'('[]'('[]'('[]'('[]'('[]'('&'(_libre,'prefix'('src_span'(51,27,51,30,1429,3),['out'(_n1)],'acq','agent_call'('src_span'(51,37,51,50,1439,13),'controleAppel',[_n1,'false',_f,_aDec]),'src_span'(51,34,51,36,1435,37))),'&'('bool_not'(_libre),'prefix'('src_span'(53,27,53,32,1501,5),['out'(_n1),'inGuard'(_n22,'val_of'('TELEPHONE','src_span'(53,39,53,48,1513,9)))],'estOc','agent_call'('src_span'(53,52,53,65,1526,13),'controleAppel',[_n1,_libre,'agent_call'('src_span'(53,75,53,82,1549,7),'removex',[_f,_n22]),_aDec]),'src_span'(53,49,53,51,1522,60))),'src_span_operator'('no_loc_info_available','src_span'(52,3,52,5,1472,2))),'&'('bool_not'(_libre),'prefix'('src_span'(55,27,55,30,1601,3),['out'(_n1)],'lib','agent_call'('src_span'(55,37,55,50,1611,13),'controleAppel',[_n1,'true',_f,_aDec]),'src_span'(55,34,55,36,1607,36))),'src_span_operator'('no_loc_info_available','src_span'(54,3,54,5,1572,2))),'&'('<'('agent_call'('src_span'(59,7,59,13,1673,6),'length',[_f]),'val_of'('nbTel','src_span'(59,19,59,24,1685,5))),'prefix'('src_span'(59,27,59,31,1693,4),['inGuard'(_n23,'val_of'('TELEPHONE','src_span'(59,35,59,44,1701,9))),'out'(_n1)],'comp','agent_call'('src_span'(59,50,59,63,1716,13),'controleAppel',[_n1,_libre,'^'(_f,'listExp'('rangeEnum'([_n23]))),_aDec]),'src_span'(59,48,59,49,1713,41))),'src_span_operator'('no_loc_info_available','src_span'(58,3,58,5,1664,2))),'repChoice'(['comprehensionGenerator'(_n24,'val_of'('TELEPHONE','src_span'(61,13,61,22,1769,9)))],'&'('bool_and'('bool_and'(_libre,'!='(_f,'listExp'('rangeEnum'([])))),'=='(_n24,'agent_call'('src_span'(64,23,64,27,1849,4),'head',[_f]))),'prefix'('src_span'(65,27,65,33,1883,6),['out'(_n1),'out'(_n24)],'acqPar','agent_call'('src_span'(65,43,65,56,1899,13),'controleAppel',[_n1,'false','listExp'('rangeEnum'([])),_aDec]),'src_span'(65,40,65,42,1895,38))),'src_span'(61,10,61,24,1766,14)),'src_span_operator'('no_loc_info_available','src_span'(60,3,60,5,1754,2))),'&'('bool_not'(_aDec),'prefix'('src_span'(70,27,70,30,1994,3),['out'(_n1)],'dec','agent_call'('src_span'(70,37,70,50,2004,13),'controleAppel',[_n1,_libre,_f,'true']),'src_span'(70,34,70,36,2000,37))),'src_span_operator'('no_loc_info_available','src_span'(67,3,67,5,1941,2))),'&'(_aDec,'prefix'('src_span'(72,27,72,30,2066,3),['out'(_n1)],'rac','agent_call'('src_span'(72,37,72,50,2076,13),'controleAppel',[_n1,_libre,_f,'false']),'src_span'(72,34,72,36,2072,38))),'src_span_operator'('no_loc_info_available','src_span'(71,3,71,5,2037,2))),'&'(_aDec,'prefix'('src_span'(74,27,74,33,2139,6),['out'(_n1)],'estDec','agent_call'('src_span'(74,40,74,53,2152,13),'controleAppel',[_n1,_libre,_f,_aDec]),'src_span'(74,37,74,39,2148,37))),'src_span_operator'('no_loc_info_available','src_span'(73,3,73,5,2110,2))),'no_loc_info_available').
'agent'('appel'(_n12),'prefix'('src_span'(78,3,78,6,2199,3),['out'(_n12)],'acq','prefix'('src_span'(79,3,79,6,2210,3),['out'(_n12)],'dec','prefix'('src_span'(80,3,80,6,2221,3),['out'(_n12)],'ton','[]'('prefix'('src_span'(82,7,82,10,2240,3),['out'(_n12)],'rac','prefix'('src_span'(83,7,83,10,2255,3),['out'(_n12)],'lib','agent_call'('src_span'(84,7,84,12,2270,5),'appel',[_n12]),'src_span'(83,14,84,6,2261,21)),'src_span'(82,14,83,6,2246,36)),'prefix'('src_span'(86,7,86,11,2291,4),['out'(_n12),'inGuard'(_n25,'val_of'('TELEPHONE','src_span'(86,18,86,27,2302,9)))],'comp','[]'('prefix'('src_span'(89,11,89,16,2366,5),['out'(_n25),'out'(_n12)],'estOc','prefix'('src_span'(90,11,90,17,2434,6),['out'(_n25)],'estDec','prefix'('src_span'(91,11,91,16,2456,5),['out'(_n12)],'tonOc','prefix'('src_span'(92,11,92,14,2477,3),['out'(_n12)],'rac','prefix'('src_span'(93,11,93,14,2496,3),['out'(_n12)],'lib','agent_call'('src_span'(94,11,94,16,2515,5),'appel',[_n12]),'src_span'(93,18,94,10,2502,25)),'src_span'(92,18,93,10,2483,44)),'src_span'(91,20,92,10,2464,63)),'src_span'(90,21,91,10,2443,84)),'src_span'(89,23,90,10,2377,150)),'prefix'('src_span'(96,11,96,17,2544,6),['out'(_n25),'out'(_n12)],'acqPar','prefix'('src_span'(97,11,97,17,2569,6),['out'(_n12),'out'(_n25)],'debSon','[]'('prefix'('src_span'(99,15,99,18,2610,3),['out'(_n12)],'rac','prefix'('src_span'(100,15,100,18,2633,3),['out'(_n12)],'lib','prefix'('src_span'(101,15,101,21,2656,6),['out'(_n12),'out'(_n25)],'finSon','prefix'('src_span'(102,15,102,18,2685,3),['out'(_n25)],'lib','agent_call'('src_span'(103,15,103,20,2708,5),'appel',[_n12]),'src_span'(102,22,103,14,2691,29)),'src_span'(101,28,102,14,2668,52)),'src_span'(100,22,101,14,2639,81)),'src_span'(99,22,100,14,2616,104)),'prefix'('src_span'(105,15,105,18,2745,3),['out'(_n25)],'dec','prefix'('src_span'(106,15,106,21,2768,6),['out'(_n12),'out'(_n25)],'finSon','prefix'('src_span'(107,15,107,19,2797,4),['out'(_n12),'out'(_n25)],'conn','[]'('prefix'('src_span'(109,19,109,22,2844,3),['out'(_n12)],'rac','prefix'('src_span'(110,19,110,24,2871,5),['out'(_n12),'out'(_n25)],'decon','prefix'('src_span'(111,19,111,22,2903,3),['out'(_n12)],'lib','prefix'('src_span'(112,19,112,22,2930,3),['out'(_n25)],'rac','prefix'('src_span'(113,19,113,22,2957,3),['out'(_n25)],'lib','agent_call'('src_span'(114,19,114,24,2984,5),'appel',[_n12]),'src_span'(113,26,114,18,2963,33)),'src_span'(112,26,113,18,2936,60)),'src_span'(111,26,112,18,2909,87)),'src_span'(110,31,111,18,2882,114)),'src_span'(109,26,110,18,2850,146)),'prefix'('src_span'(116,19,116,22,3029,3),['out'(_n25)],'rac','prefix'('src_span'(117,19,117,24,3056,5),['out'(_n12),'out'(_n25)],'decon','prefix'('src_span'(118,19,118,22,3088,3),['out'(_n25)],'lib','prefix'('src_span'(119,19,119,22,3115,3),['out'(_n12)],'rac','prefix'('src_span'(120,19,120,22,3142,3),['out'(_n12)],'lib','agent_call'('src_span'(121,19,121,24,3169,5),'appel',[_n12]),'src_span'(120,26,121,18,3148,33)),'src_span'(119,26,120,18,3121,60)),'src_span'(118,26,119,18,3094,87)),'src_span'(117,31,118,18,3067,114)),'src_span'(116,26,117,18,3035,146)),'src_span_operator'('no_loc_info_available','src_span'(115,15,115,17,3008,2))),'src_span'(107,26,108,14,2807,390)),'src_span'(106,28,107,14,2780,417)),'src_span'(105,22,106,14,2751,446)),'src_span_operator'('no_loc_info_available','src_span'(104,11,104,13,2728,2))),'src_span'(97,24,98,10,2581,628)),'src_span'(96,24,97,10,2556,653)),'src_span_operator'('no_loc_info_available','src_span'(95,7,95,9,2531,2))),'src_span'(86,28,87,6,2311,916)),'src_span_operator'('no_loc_info_available','src_span'(85,3,85,5,2282,2))),'src_span'(80,10,81,2,2227,994)),'src_span'(79,10,80,2,2216,1005)),'src_span'(78,10,79,2,2205,1016)),'src_span'(78,3,125,4,2199,1019)).
'assertModelCheckExt'('False','val_of'('Main','src_span'(128,8,128,12,3279,4)),'DeadlockFree','F').
'bindval'('Prop1','repInterleave'(['comprehensionGenerator'(_n3,'val_of'('TELEPHONE','src_span'(129,16,129,25,3322,9)))],'agent_call'('src_span'(129,29,129,38,3335,9),'Prop1Body',[_n3]),'src_span'(129,12,129,27,3318,15)),'src_span'(129,1,129,41,3307,40)).
'agent'('Prop1Body'(_n4),'prefix'('src_span'(131,5,131,8,3367,3),['out'(_n4)],'dec','prefix'('src_span'(132,5,132,8,3380,3),['out'(_n4)],'rac','agent_call'('src_span'(133,5,133,14,3393,9),'Prop1Body',[_n4]),'src_span'(132,11,133,4,3385,22)),'src_span'(131,11,132,4,3372,35)),'src_span'(131,5,133,17,3367,38)).
'assertRef'('False','val_of'('Prop1','src_span'(135,8,135,13,3414,5)),'Trace','\x5c\'('val_of'('Main','src_span'(135,20,135,24,3426,4)),'agent_call'('src_span'(135,27,135,32,3433,5),'union',['val_of'('CTRL','src_span'(135,33,135,37,3439,4)),'closure'(['ton','tonOc','comp','debSon','finSon','conn','decon'])]),'src_span_operator'('no_loc_info_available','src_span'(135,25,135,26,3431,1))),'src_span'(135,1,135,91,3407,90)).
'comment'('lineComment'('-- Utility definitions\xd\'),'src_position'(1,1,0,23)).
'comment'('lineComment'('-- removes x from sequence l\xd\'),'src_position'(3,1,26,29)).
'comment'('lineComment'('--'),'src_position'(2,1,22,2)).
'comment'('lineComment'('-- Specification d\x27\un systeme telephonique en CSP.'),'src_position'(3,1,25,50)).
'comment'('lineComment'('-- Marc Frappier'),'src_position'(4,1,76,16)).
'comment'('lineComment'('-- Universit\xe9\ de Sherbrooke'),'src_position'(5,1,93,27)).
'comment'('lineComment'('--'),'src_position'(6,1,121,2)).
'comment'('lineComment'('--'),'src_position'(7,1,124,2)).
'comment'('lineComment'('-- Si deux utilisateurs appellent le m\xea\me t\xe9\l\xe9\phone,'),'src_position'(8,1,127,52)).
'comment'('lineComment'('-- le premier qui a compos\xe9\ le numero obtiens la communication.'),'src_position'(9,1,180,63)).
'comment'('lineComment'('--'),'src_position'(10,1,244,2)).
'comment'('lineComment'('-- Par exemple, pour la s\xe9\quence'),'src_position'(11,1,247,32)).
'comment'('lineComment'('--     dec!n1,dec!n2,comp!n1!n3,comp!n2!n3!'),'src_position'(12,1,280,43)).
'comment'('lineComment'('-- il y a une seule suite possible:'),'src_position'(13,1,324,35)).
'comment'('lineComment'('--     debutSonnerie!n1,n3!,tonOccupe!n2'),'src_position'(14,1,360,40)).
'comment'('lineComment'('-- actions du syst\xe8\me t\xe9\l\xe9\phonique'),'src_position'(20,1,437,34)).
'comment'('lineComment'('-- actions internes utilis\xe9\es pour le contr\xf4\le; \xe0\ masquer dans le comportement final'),'src_position'(24,1,577,84)).
'comment'('blockComment'('{-\xa\ libre == le t\xe9\l\xe9\phone n1 n\x27\a pas d\xe9\croch\xe9\ pour r\xe9\pondre \xe0\ un autre appel;\xa\          permet de choisir o\xf9\ dec s\x27\ex\xe9\cute:\xa\              i) pour appeler quelqu\x27\un, ou bien\xa\              ii) pour r\xe9\pondre \xe0\ un appel\xa\ f == file d\x27\attente de ceux qui ont compos\xe9\\xa\ aDec == indique si le t\xe9\l\xe9\phone n1 a d\xe9\croch\xe9\\xa\-}'),'src_position'(39,1,1030,310)).
'comment'('lineComment'('-- mise \xe0\ jour de libre'),'src_position'(50,1,1379,23)).
'comment'('lineComment'('-- mise \xe0\ jour de f'),'src_position'(57,1,1642,19)).
'comment'('lineComment'('-- mise a jour de aDec'),'src_position'(69,1,1945,22)).
'comment'('lineComment'('-- n2 est d\xe9\j\xe0\ d\xe9\croch\xe9\'),'src_position'(88,11,2332,23)).
'comment'('lineComment'('-- supprime n1 de la file d\x27\attente de n2'),'src_position'(89,27,2382,41)).
'comment'('lineComment'('-- Dec et rac forme un cycle dans toutes les traces'),'src_position'(127,1,3220,51)).
'symbol'('removex','removex','src_span'(4,1,4,8,56,7),'Funktion or Process').
'symbol'('l','l','src_span'(4,9,4,10,64,1),'Ident (Prolog Variable)').
'symbol'('x','x','src_span'(4,11,4,12,66,1),'Ident (Prolog Variable)').
'symbol'('head','head','src_span'(7,19,7,23,123,4),'BuiltIn primitive').
'symbol'('tail','tail','src_span'(8,12,8,16,144,4),'BuiltIn primitive').
'symbol'('nbTel','nbTel','src_span'(17,1,17,6,403,5),'Ident (Groundrep.)').
'symbol'('TELEPHONE','TELEPHONE','src_span'(18,1,18,10,413,9),'Ident (Groundrep.)').
'symbol'('dec','dec','src_span'(21,9,21,12,480,3),'Channel').
'symbol'('rac','rac','src_span'(21,14,21,17,485,3),'Channel').
'symbol'('ton','ton','src_span'(21,19,21,22,490,3),'Channel').
'symbol'('tonOc','tonOc','src_span'(21,24,21,29,495,5),'Channel').
'symbol'('comp','comp','src_span'(22,9,22,13,521,4),'Channel').
'symbol'('debSon','debSon','src_span'(22,15,22,21,527,6),'Channel').
'symbol'('finSon','finSon','src_span'(22,23,22,29,535,6),'Channel').
'symbol'('conn','conn','src_span'(22,31,22,35,543,4),'Channel').
'symbol'('decon','decon','src_span'(22,37,22,42,549,5),'Channel').
'symbol'('acq','acq','src_span'(25,9,25,12,670,3),'Channel').
'symbol'('lib','lib','src_span'(25,14,25,17,675,3),'Channel').
'symbol'('estDec','estDec','src_span'(25,19,25,25,680,6),'Channel').
'symbol'('estOc','estOc','src_span'(26,9,26,14,714,5),'Channel').
'symbol'('acqPar','acqPar','src_span'(26,16,26,22,721,6),'Channel').
'symbol'('SYNC','SYNC','src_span'(28,1,28,5,751,4),'Ident (Groundrep.)').
'symbol'('CTRL','CTRL','src_span'(29,1,29,5,779,4),'Ident (Groundrep.)').
'symbol'('Main','Main','src_span'(31,1,31,5,825,4),'Ident (Groundrep.)').
'symbol'('union','union','src_span'(31,23,31,28,847,5),'BuiltIn primitive').
'symbol'('MainEnv','MainEnv','src_span'(33,1,33,8,888,7),'Ident (Groundrep.)').
'symbol'('tousAppels','tousAppels','src_span'(35,1,35,11,911,10),'Ident (Groundrep.)').
'symbol'('n','n','src_span'(35,18,35,19,928,1),'Ident (Prolog Variable)').
'symbol'('controleTousAppels','controleTousAppels','src_span'(37,1,37,19,954,18),'Ident (Groundrep.)').
'symbol'('n2','n','src_span'(37,26,37,27,979,1),'Ident (Prolog Variable)').
'symbol'('controleAppel','controleAppel','src_span'(48,1,48,14,1342,13),'Funktion or Process').
'symbol'('n1','n1','src_span'(48,15,48,17,1356,2),'Ident (Prolog Variable)').
'symbol'('libre','libre','src_span'(48,19,48,24,1360,5),'Ident (Prolog Variable)').
'symbol'('f','f','src_span'(48,26,48,27,1367,1),'Ident (Prolog Variable)').
'symbol'('aDec','aDec','src_span'(48,29,48,33,1370,4),'Ident (Prolog Variable)').
'symbol'('n22','n2','src_span'(53,36,53,38,1510,2),'Ident (Prolog Variable)').
'symbol'('length','length','src_span'(59,7,59,13,1673,6),'BuiltIn primitive').
'symbol'('n23','n2','src_span'(59,32,59,34,1698,2),'Ident (Prolog Variable)').
'symbol'('n24','n2','src_span'(61,10,61,12,1766,2),'Ident (Prolog Variable)').
'symbol'('head','head','src_span'(64,23,64,27,1849,4),'BuiltIn primitive').
'symbol'('appel','appel','src_span'(76,1,76,6,2184,5),'Funktion or Process').
'symbol'('n12','n1','src_span'(76,7,76,9,2190,2),'Ident (Prolog Variable)').
'symbol'('n25','n2','src_span'(86,15,86,17,2299,2),'Ident (Prolog Variable)').
'symbol'('Prop1','Prop1','src_span'(129,1,129,6,3307,5),'Ident (Groundrep.)').
'symbol'('n3','n','src_span'(129,12,129,13,3318,1),'Ident (Prolog Variable)').
'symbol'('Prop1Body','Prop1Body','src_span'(130,1,130,10,3348,9),'Funktion or Process').
'symbol'('n4','n','src_span'(130,11,130,12,3358,1),'Ident (Prolog Variable)').
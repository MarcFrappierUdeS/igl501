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
'bindval'('X','setExp'('rangeClosed'('int'(1),'int'(3))),'src_span'(4,1,4,11,55,10)).
'channel'('a','type'('dotUnitType')).
'channel'('b','type'('dotUnitType')).
'channel'('c','type'('dotUnitType')).
'channel'('d','type'('dotUnitType')).
'channel'('e','type'('dotTupleType'(['setExp'('rangeClosed'('int'(0),'int'(3)))]))).
'channel'('f','type'('dotTupleType'(['setExp'('rangeClosed'('int'(0),'int'(3)))]))).
'bindval'('P0','prefix'('src_span'(9,6,9,7,111,1),[],'a','prefix'('src_span'(9,11,9,12,116,1),[],'b','skip'('src_span'(9,16,9,20,121,4)),'src_span'(9,13,9,15,117,9)),'src_span'(9,8,9,10,112,14)),'src_span'(9,1,9,20,106,19)).
'bindval'('P1','prefix'('src_span'(11,6,11,7,132,1),[],'c','prefix'('src_span'(11,11,11,12,137,1),[],'d','stop'('src_span'(11,16,11,20,142,4)),'src_span'(11,13,11,15,138,9)),'src_span'(11,8,11,10,133,14)),'src_span'(11,1,11,20,127,19)).
'bindval'('P2','[]'('val_of'('P0','src_span'(13,6,13,8,153,2)),'val_of'('P1','src_span'(13,12,13,14,159,2)),'src_span_operator'('no_loc_info_available','src_span'(13,9,13,11,156,2))),'src_span'(13,1,13,14,148,13)).
'bindval'('P2_int','|~|'('val_of'('P0','src_span'(15,10,15,12,189,2)),'val_of'('P1','src_span'(15,17,15,19,196,2)),'src_span_operator'('no_loc_info_available','src_span'(15,13,15,16,192,3))),'src_span'(15,1,15,19,180,18)).
'bindval'('P3','[]'(';'('skip'('src_span'(17,7,17,11,223,4)),'prefix'('src_span'(17,15,17,16,231,1),[],'a','stop'('src_span'(17,20,17,24,236,4)),'src_span'(17,17,17,19,232,9)),'src_span_operator'('no_loc_info_available','src_span'(17,12,17,13,228,1))),'prefix'('src_span'(17,30,17,31,246,1),[],'b','stop'('src_span'(17,35,17,39,251,4)),'src_span'(17,32,17,34,247,9)),'src_span_operator'('no_loc_info_available','src_span'(17,27,17,29,243,2))),'src_span'(17,1,17,39,217,38)).
'bindval'('P4',';'('val_of'('P0','src_span'(19,6,19,8,262,2)),'val_of'('P1','src_span'(19,11,19,13,267,2)),'src_span_operator'('no_loc_info_available','src_span'(19,9,19,10,265,1))),'src_span'(19,1,19,13,257,12)).
'bindval'('P4_inv',';'('val_of'('P1','src_span'(21,10,21,12,280,2)),'val_of'('P0','src_span'(21,15,21,17,285,2)),'src_span_operator'('no_loc_info_available','src_span'(21,13,21,14,283,1))),'src_span'(21,1,21,17,271,16)).
'bindval'('P5','\x5c\'('val_of'('P4','src_span'(23,6,23,8,294,2)),'setExp'('rangeEnum'(['a','b'])),'src_span_operator'('no_loc_info_available','src_span'(23,9,23,10,297,1))),'src_span'(23,1,23,16,289,15)).
'bindval'('P6',';'('sharing'('setExp'('rangeEnum'(['b'])),'prefix'('src_span'(26,14,26,15,325,1),[],'a','prefix'('src_span'(26,19,26,20,330,1),[],'b','skip'('src_span'(26,24,26,28,335,4)),'src_span'(26,21,26,23,331,9)),'src_span'(26,16,26,18,326,14)),'prefix'('src_span'(28,14,28,15,355,1),[],'b','prefix'('src_span'(28,19,28,20,360,1),[],'c','skip'('src_span'(28,24,28,28,365,4)),'src_span'(28,21,28,23,361,9)),'src_span'(28,16,28,18,356,14)),'src_span'(28,3,28,12,344,9)),'prefix'('src_span'(30,3,30,4,377,1),[],'d','stop'('src_span'(30,8,30,12,382,4)),'src_span'(30,5,30,7,378,9)),'src_span_operator'('no_loc_info_available','src_span'(30,1,30,2,375,1))),'src_span'(25,1,30,12,307,79)).
'bindval'('P7','prefix'('src_span'(32,6,32,7,393,1),['inGuard'(_x,'val_of'('X','src_span'(32,10,32,11,397,1)))],'e','&'('<'(_x,'int'(3)),'prefix'('src_span'(32,25,32,26,412,1),[],'a','prefix'('src_span'(32,30,32,31,417,1),['out'(_x)],'f','stop'('src_span'(32,37,32,41,424,4)),'src_span'(32,34,32,36,420,10)),'src_span'(32,27,32,29,413,16))),'src_span'(32,12,32,15,398,35)),'src_span'(32,1,32,42,388,41)).
'bindval'('P8','[]'(';'('|||'('prefix'('src_span'(34,8,34,9,438,1),[],'a','skip'('src_span'(34,13,34,17,443,4)),'src_span'(34,10,34,12,439,9)),'prefix'('src_span'(34,22,34,23,452,1),[],'b','skip'('src_span'(34,27,34,31,457,4)),'src_span'(34,24,34,26,453,9)),'src_span_operator'('no_loc_info_available','src_span'(34,18,34,21,448,3))),'prefix'('src_span'(34,35,34,36,465,1),[],'c','stop'('src_span'(34,39,34,43,469,4)),'src_span'(34,37,34,38,466,8)),'src_span_operator'('no_loc_info_available','src_span'(34,33,34,34,463,1))),'prefix'('src_span'(34,49,34,50,479,1),[],'d','stop'('src_span'(34,54,34,58,484,4)),'src_span'(34,51,34,53,480,9)),'src_span_operator'('no_loc_info_available','src_span'(34,46,34,48,476,2))),'src_span'(34,1,34,58,431,57)).
'bindval'('P9','|||'('val_of'('P0','src_span'(36,6,36,8,496,2)),'val_of'('P0','src_span'(36,13,36,15,503,2)),'src_span_operator'('no_loc_info_available','src_span'(36,9,36,12,499,3))),'src_span'(36,1,36,15,491,14)).
'bindval'('P10',';'('prefix'('src_span'(38,8,38,9,514,1),[],'a','prefix'('src_span'(38,13,38,14,519,1),[],'b','skip'('src_span'(38,18,38,22,524,4)),'src_span'(38,15,38,17,520,9)),'src_span'(38,10,38,12,515,14)),'prefix'('src_span'(38,27,38,28,533,1),[],'c','stop'('src_span'(38,32,38,36,538,4)),'src_span'(38,29,38,31,534,9)),'src_span_operator'('no_loc_info_available','src_span'(38,25,38,26,531,1))),'src_span'(38,1,38,36,507,35)).
'bindval'('P11','repInterleave'(['comprehensionGenerator'(_x2,'setExp'('rangeClosed'('int'(0),'int'(2))))],'prefix'('src_span'(40,24,40,27,567,3),[],'dotTuple'(['e',_x2]),'stop'('src_span'(40,31,40,35,574,4)),'src_span'(40,28,40,30,570,11)),'src_span'(40,11,40,23,554,12)),'src_span'(40,1,40,35,544,34)).
'comment'('lineComment'('-- ex1'),'src_position'(1,1,0,6)).
'comment'('lineComment'('-- D\xe9\finition de Sigma (l\x27\alphabet du syst\xe8\me)'),'src_position'(3,1,8,46)).
'comment'('lineComment'('-- choix externe'),'src_position'(13,15,162,16)).
'comment'('lineComment'('-- choix externe'),'src_position'(15,20,199,16)).
'symbol'('X','X','src_span'(4,1,4,2,55,1),'Ident (Groundrep.)').
'symbol'('a','a','src_span'(6,9,6,10,75,1),'Channel').
'symbol'('b','b','src_span'(6,11,6,12,77,1),'Channel').
'symbol'('c','c','src_span'(6,14,6,15,80,1),'Channel').
'symbol'('d','d','src_span'(6,16,6,17,82,1),'Channel').
'symbol'('e','e','src_span'(7,9,7,10,92,1),'Channel').
'symbol'('f','f','src_span'(7,11,7,12,94,1),'Channel').
'symbol'('P0','P0','src_span'(9,1,9,3,106,2),'Ident (Groundrep.)').
'symbol'('P1','P1','src_span'(11,1,11,3,127,2),'Ident (Groundrep.)').
'symbol'('P2','P2','src_span'(13,1,13,3,148,2),'Ident (Groundrep.)').
'symbol'('P2_int','P2_int','src_span'(15,1,15,7,180,6),'Ident (Groundrep.)').
'symbol'('P3','P3','src_span'(17,1,17,3,217,2),'Ident (Groundrep.)').
'symbol'('P4','P4','src_span'(19,1,19,3,257,2),'Ident (Groundrep.)').
'symbol'('P4_inv','P4_inv','src_span'(21,1,21,7,271,6),'Ident (Groundrep.)').
'symbol'('P5','P5','src_span'(23,1,23,3,289,2),'Ident (Groundrep.)').
'symbol'('P6','P6','src_span'(25,1,25,3,307,2),'Ident (Groundrep.)').
'symbol'('P7','P7','src_span'(32,1,32,3,388,2),'Ident (Groundrep.)').
'symbol'('x','x','src_span'(32,8,32,9,395,1),'Ident (Prolog Variable)').
'symbol'('P8','P8','src_span'(34,1,34,3,431,2),'Ident (Groundrep.)').
'symbol'('P9','P9','src_span'(36,1,36,3,491,2),'Ident (Groundrep.)').
'symbol'('P10','P10','src_span'(38,1,38,4,507,3),'Ident (Groundrep.)').
'symbol'('P11','P11','src_span'(40,1,40,4,544,3),'Ident (Groundrep.)').
'symbol'('x2','x','src_span'(40,11,40,12,554,1),'Ident (Prolog Variable)').
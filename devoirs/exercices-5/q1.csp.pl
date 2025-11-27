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
'channel'('a','type'('dotUnitType')).
'channel'('b','type'('dotUnitType')).
'channel'('c','type'('dotUnitType')).
'channel'('d','type'('dotUnitType')).
'bindval'('P',';'('[]'('sharing'('closure'(['a']),'prefix'('src_span'(3,8,3,9,24,1),[],'a','skip'('src_span'(3,11,3,15,27,4)),'src_span'(3,10,3,10,25,7)),'prefix'('src_span'(3,26,3,27,42,1),[],'b','skip'('src_span'(3,29,3,33,45,4)),'src_span'(3,28,3,28,43,7)),'src_span'(3,16,3,25,32,9)),'prefix'('src_span'(3,39,3,40,55,1),[],'c','skip'('src_span'(3,42,3,46,58,4)),'src_span'(3,41,3,41,56,7)),'src_span_operator'('no_loc_info_available','src_span'(3,36,3,38,52,2))),'prefix'('src_span'(3,48,3,49,64,1),[],'d','stop'('src_span'(3,51,3,55,67,4)),'src_span'(3,50,3,50,65,7)),'src_span_operator'('no_loc_info_available','src_span'(3,47,3,48,63,1))),'src_span'(3,1,3,55,17,54)).
'symbol'('a','a','src_span'(1,9,1,10,8,1),'Channel').
'symbol'('b','b','src_span'(1,11,1,12,10,1),'Channel').
'symbol'('c','c','src_span'(1,13,1,14,12,1),'Channel').
'symbol'('d','d','src_span'(1,15,1,16,14,1),'Channel').
'symbol'('P','P','src_span'(3,1,3,2,17,1),'Ident (Groundrep.)').
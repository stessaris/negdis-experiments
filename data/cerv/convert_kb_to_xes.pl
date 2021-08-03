
fold :- fold01, fold02, fold03, fold04, fold05.

fold01 :-
    convert('./fold01/cerv.01.kb', './fold01/cerv.01.pos.xes', './fold01/cerv.01.neg.xes')
    , convert('./fold01/cerv.01.val.kb', './fold01/cerv.01.valpos.xes', './fold01/cerv.01.valneg.xes').

fold02 :-
    convert('./fold02/cerv.02.kb', './fold02/cerv.02.pos.xes', './fold02/cerv.02.neg.xes')
    , convert('./fold02/cerv.02.val.kb', './fold02/cerv.02.valpos.xes', './fold02/cerv.02.valneg.xes').

fold03 :-
    convert('./fold03/cerv.03.kb', './fold03/cerv.03.pos.xes', './fold03/cerv.03.neg.xes')
    , convert('./fold03/cerv.03.val.kb', './fold03/cerv.03.valpos.xes', './fold03/cerv.03.valneg.xes').

fold04 :-
    convert('./fold04/cerv.04.kb', './fold04/cerv.04.pos.xes', './fold04/cerv.04.neg.xes')
    , convert('./fold04/cerv.04.val.kb', './fold04/cerv.04.valpos.xes', './fold04/cerv.04.valneg.xes').

fold05 :-
    convert('./fold05/cerv.05.kb', './fold05/cerv.05.pos.xes', './fold05/cerv.05.neg.xes')
    , convert('./fold05/cerv.05.val.kb', './fold05/cerv.05.valpos.xes', './fold05/cerv.05.valneg.xes').

% convert(InputFileName, OutputFileNamePos, OutputFileNameNeg)
convert(InputFileName, OutputFileNamePos, OutputFileNameNeg) :-
    open( InputFileName, read, InputStream)
    , open( OutputFileNamePos, write, OutputPos)
    , open( OutputFileNameNeg, write, OutputNeg)
    , write_preamble(OutputPos)
    , write_preamble(OutputNeg)
    , read_all_models(InputStream, OutputPos, OutputNeg)
    , write_closing(OutputPos)
    , write_closing(OutputNeg)
    , close(InputStream)
    , close(OutputPos)
    , close(OutputNeg)
    .


% read_all_models(InputStream, OutputPos, OutputNeg)
read_all_models(InputStream, OutputPos, OutputNeg) :-
    read_model(InputStream, TraceId, Trace, PosNeg)
    , !
    , ( (PosNeg = pos) ->
            write_trace(TraceId, Trace, OutputPos)
        ;
            write_trace(TraceId, Trace, OutputNeg)
    )
    , read_all_models(InputStream, OutputPos, OutputNeg)
    .

read_all_models(_InputStream, _OutputPos, _OutputNeg).


% read_model(InputStream, TraceId, Trace, PosNeg)
read_model(InputStream, TraceId, Trace, PosNeg) :-
    read( InputStream, begin(model(TraceId)) )
    , !
    , read_events(InputStream, Trace, PosNeg)
    , read( InputStream, end(model(TraceId)))
    .

% read_events(InputStream, Trace, PosNeg)
read_events(InputStream, Trace, PosNeg) :-
    read(InputStream, Event)
    , ( (Event = hap(_Desc, _X, _Timestamp)) ->
            translate_event(Event, TEvent)
            , Trace = [TEvent | TTrace]
            , read_events(InputStream, TTrace, PosNeg)
        ;
            Event = PosNeg
            , Trace = []
    )
    .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Specific filtering
translate_event(
    hap(performed(activity(eseguiEsame,_Originator,[_,tipoEsame(TE)])),_,TimeStamp)
    , event(Desc, TimeStamp)
) :-
    !, atom_concat(eseguiEsame_, TE, Desc).
translate_event(
    hap(performed(activity(invioCampione,_Originator,[_,tipoEsame(TE)])),_,TimeStamp)
    , event(Desc, TimeStamp)
) :-
    !, atom_concat(invioCampione_, TE, Desc).
translate_event(
    hap(performed(activity(invioLetteraNegativaBiopsia,_Originator,[_])),_, TimeStamp)
    , event(invioLetteraNegativaBiopsia, TimeStamp)
) :- !.
translate_event(
    hap(performed(activity(invioLetteraNegativaPapTest,_Originator,[_])),_, TimeStamp)
    , event(invioLetteraNegativaPapTest, TimeStamp)
) :- !.
translate_event(
    hap(performed(activity(invioRisultato,_Originator,[esito(ES),_,tipoEsame(TE)])),_, TimeStamp)
    , event(Desc, TimeStamp)
) :-
    !, atom_concat(invioRisultato_, ES, Part)
    , atom_concat(Part, TE, Desc).
translate_event(
    hap(performed(activity(telefonataPositivi,_Originator,[tipoEsame(TE)])),_, TimeStamp)
    , event(Desc, TimeStamp)
) :-
    !, atom_concat(telefonataPositivi, TE, Desc).
translate_event(
    hap(performed(activity(Activity,_Originator,_)),_, TimeStamp)
    , event(Activity, TimeStamp)
).






% print_single_events_xes(Stream, [abd(_,event(Event),Timestamp) |T], TraceId) :-
% 	get_time(CurrentTime)
% 	, CurrentTimestamp is CurrentTime + Timestamp 
% 	, format_time(string(StampString), '%FT%T.000%:z', CurrentTimestamp)
% 	, atomics_to_string([
% 		'\t\t<event>\n'
%       	, '\t\t\t<string key="concept:name" value="', Event, '"></string>\n'
%       	, '\t\t\t<date key="time:timestamp" value="', StampString, '"></date>\n'
% 		, '\t\t\t<string key="lifecycle:transition" value="complete"/>\n'
%     	, '\t\t</event>\n'
% 	], XMLEvent)




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Writing traces in XES
% write_trace(TraceId, Trace, _Stream) :-
%     write(TraceId), nl
%     , write(Trace), nl
%     , nl, nl.
write_trace(TraceId, Trace, Stream) :-
    write_trace_preamble(TraceId, Stream)
    , write_events(Trace, Stream)
    , write_trace_closing(Stream)
    .


write_events([Event | T], Stream) :-
    write_event(Event, Stream)
    , write_events(T, Stream).
write_events([], _Stream).


write_event(event(Desc,TimeStamp), Stream) :-
	get_time(CurrentTime)
	, CurrentTimestamp is CurrentTime + TimeStamp 
	, format_time(string(StampString), '%FT%T.000%:z', CurrentTimestamp)
	, atomics_to_string([
		'\t\t<event>\n'
      	, '\t\t\t<string key="concept:name" value="', Desc, '"></string>\n'
      	, '\t\t\t<date key="time:timestamp" value="', StampString, '"></date>\n'
		, '\t\t\t<string key="lifecycle:transition" value="complete"/>\n'
    	, '\t\t</event>\n'
	], XMLEvent)
    , write(Stream, XMLEvent)
    .

write_trace_preamble(TraceId, Stream) :-
    atomics_to_string([
		'\t<trace>\n'
    	, '\t\t<string key="concept:name" value="', TraceId, '" />\n'
	], TracePreamble)
	, write(Stream, TracePreamble).
write_trace_closing(Stream) :-
    atomics_to_string(['\t</trace>\n'], TraceClosing)
	, write(Stream, TraceClosing)
    .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preamble and closing in XES
write_preamble(Stream) :-
    atomics_to_string([
		'<?xml version="1.0" ?>\n'
		, '<log xes.version="1.0" xmlns="http://www.xes-standard.org/">\n'
  		, '\t<extension name="Concept" prefix="concept" uri="http://www.xes-standard.org/concept.xesext"></extension>\n'
  		, '\t<extension name="Time" prefix="time" uri="http://www.xes-standard.org/time.xesext"></extension>\n'
	], Preamble)
	, write(Stream, Preamble)
    .

write_closing(Stream) :-
    atomics_to_string(['</log>'], Closing)
    , write(Stream, Closing).
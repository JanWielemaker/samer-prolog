:- module(sparkle,[
      sparql_endpoint/2
   ,  sparql_endpoint/3
   ,  sparql_prefix/2			% +Prefix, +URL
   ,  current_sparql_prefix/2		% ?Prefix, ?URL
   ,  current_sparql_endpoint/5
   ,  query_goal/3     % Endpoint, Context, Opts
   ,  query_phrase/3   % Endpoint, QueryPhrase, Result
   ,  query_sparql/3 % Endpoint,QueryText,Result
   ,  (??)/1
   ,  (??)/2
   ,  op(1150,fx,??)
   ,  op(1150,xfy,??)
	]).

/** <module> Query to SPARQL endpoints with a more Prolog-like syntax

  Samer Abdallah, Dept. of Computer Science, UCL (2014)
  Based on Yves Raimond's swic package, but completely re-written.

   This module provides a little language for expressing SPARQL queries
   and a database of known SPARQL endpoints. Queries can be executed
   across multiple endpoints in parallel. When using auto-paging,
   multiple queries are made automatically to fetch new bindings as
   they are needed. For example,
   ==
   EP ?? rdf(A,B,C).
   ==
   will retrieve all triples from all endpoints in parallel, fetching
   100 bindings at a time from each endpoint (assuming the setting
   sparkle:limit takes it's default value of 100).
*/

:- use_module(library(debug)).
:- use_module(library(error)).
:- use_module(library(uri)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(settings)).
:- use_module(library(option)).
:- use_module(library(semweb/sparql_client)).
:- use_module(library(dcg_core)).
:- use_module(library(dcg_codes)).
:- use_module(sparql_dcg).
:- use_module(concurrency).


:- dynamic sparql_endpoint/5.
:- multifile sparql_endpoint/5.
:- set_prolog_flag(double_quotes, codes).

:- setting(limit,integer,100,'Default SPARQL SELECT limit').
:- setting(select_options,list,[distinct(true)],'Default select options').

:- meta_predicate
	sparql_endpoint(:,+),
	sparql_endpoint(:,+,+),
	sparql_prefix(:,+),
	current_sparql_endpoint(:,?,?,?,?),
	current_sparql_prefix(:,-),
	query_goal(:,?,+),
	query_phrase(:,//,-),
	query_sparql(:,?,+),
	??(:,+).


%% '??'(+Goal:sparql_goal) is nondet.
%  Equivalent to _ ?? Goal. Will query all endpoints
%  in parallel. Identical bindings may be returned multiple times.
%  See query_goal/3 for details.
??(Spec) :- ??(_,Spec).

%% '??'(EP,+Goal:sparql_goal) is nondet.
%  Equivalent to query_goal(EP,Goal,Opts) where Opts is the value of
%  the setting sparkle:select_options. See query_goal/3 for details.
%  IF EP is unbound on entry, it is bound to the endpoint from which
%  the current bindings were obtained.
??(EP,Spec) :-
   spec_goal_opts(Spec,Goal,Opts),
   setting(select_options,Opts0),
   merge_options(Opts,Opts0,Opts1),
   query_goal(EP,Goal,Opts1).

spec_goal_opts(Opts ?? Goal, Goal, Opts) :- !.
spec_goal_opts(Goal,Goal,[]).

/*
 * Assert/declare a new sparql end point
 */

%% sparql_endpoint(:EP:ground, +URL:atom, +Options) is det.
%% sparql_endpoint(:EP:ground, +URL:atom) is det.
%
%  Declares EP as a short name for a SPARQL endpoint with the given URL.
%  No options are defined at the moment.
sparql_endpoint(EP,Url) :- sparql_endpoint(EP,Url,[]).
sparql_endpoint(M:EP,Url,Options) :-
   url_endpoint(Url,Host,Port,Path),
   (   current_predicate(M:sparql_endpoint/5),
       M:sparql_endpoint(EP,_,_,_,_)
   ->  print_message(warning, sparkle(updated_endpoint(EP, Url))),
       retractall(M:sparql_endpoint(EP,_,_,_,_))
   ;   true
   ),
   debug(sparkle,'Asserting SPARQL end point ~w: ~w ~w ~w ~w.',[EP,Host,Port,Path,Options]),
   assert(M:sparql_endpoint(EP,Host,Port,Path,Options)).

user:term_expansion(:-(sparql_endpoint(EP,Url)), Expanded) :-
   endpoint_declaration(EP,Url,[],Expanded).
user:term_expansion(:-(sparql_endpoint(EP,Url,Options)), Expanded) :-
   endpoint_declaration(EP,Url,Options,Expanded).

endpoint_declaration(EP,Url,Options, sparql_endpoint(EP,Host,Port,Path,Options)) :-
    debug(sparkle,'Declaring SPARQL end point ~w: ~w ~w ~w ~w.',[EP,Host,Port,Path,Options]),
    url_endpoint(Url,Host,Port,Path).

url_endpoint(Url,Host,Port,Path) :-
    uri_components(Url, Components),
    uri_data(authority, Components, Authority),
    uri_authority_components(Authority, AuthComponents),
    uri_authority_data(host, AuthComponents, Host),
    uri_authority_data(port, AuthComponents, Port),
    uri_data(path, Components, Path),
    (	var(Port)
    ->	uri_data(scheme, Components, Scheme),
	scheme_default_port(Scheme, Port)
    ;	true
    ).

scheme_default_port(http, 80).
scheme_default_port(https, 443).

%% current_sparql_endpoint(-EP:ground,-Host:atom,-Port:natural,-Path:atom,-Options:list) is nondet.
%
%  Succeeds once for each known endpoint.
current_sparql_endpoint(M0:EP,Host,Port,Path,Options) :-
   default_module(M0,M),
   current_predicate(M:sparql_endpoint/5),
   M:sparql_endpoint(EP,Host,Port,Path,Options).

%% sparql_prefix(+Prefix,+Url) is det.
%
% Register a prefix for use with SPARQL queries

sparql_prefix(M:Prefix, URL) :-
    must_be(atom, Prefix),
    must_be(atom, URL),
    M:assert('sparql prefix'(Prefix, URL)).

user:term_expansion(sparql_prefix(Prefix,URL),
		    'sparql prefix'(Prefix, URL)) :-
    must_be(atom, Prefix),
    must_be(atom, URL).

%% current_sparql_prefix(:Prefix, ?URL) is nondet.
%
%  True when Prefix is a registered prefix for URL.

current_sparql_prefix(M0:Prefix, URL) :-
    default_module(M0,M),
    current_predicate(M:'sparql prefix'/2),
    M:'sparql prefix'(Prefix, URL).
current_sparql_prefix(_:Prefix, URL) :-
    (	current_predicate(rdf_db:ns/2)
    ->	rdf_db:ns(Prefix, URL)
    ;	default_prefix(Prefix, URL)
    ).

default_prefix(rdf,	'http://www.w3.org/1999/02/22-rdf-syntax-ns#').
default_prefix(rdfs,	'http://www.w3.org/2000/01/rdf-schema#').
default_prefix(owl,	'http://www.w3.org/2002/07/owl#').
default_prefix(xsd,	'http://www.w3.org/2001/XMLSchema#').
default_prefix(dc,	'http://purl.org/dc/elements/1.1/').
default_prefix(dcterms,	'http://purl.org/dc/terms/').
default_prefix(eor,	'http://dublincore.org/2000/03/13/eor#').
default_prefix(skos,	'http://www.w3.org/2004/02/skos/core#').
default_prefix(foaf,	'http://xmlns.com/foaf/0.1/').
default_prefix(void,	'http://rdfs.org/ns/void#').

%% expand_prefixes(+TermIn, +Module, -Term)
%
%  Expand prefixes in TermIn for the given context Module.

expand_prefixes(Var, _, VarOut) :-
    var(Var), !,
    VarOut = Var.
expand_prefixes(P:L, M, URL) :- !,
    must_be(atom, P),
    (	current_sparql_prefix(M:P, Ex)
    ->	atom_concat(Ex, L, URL)
    ;	existence_error(prefix, P)
    ).
expand_prefixes(In, M, Out) :-
    compound(In), !,
    compound_name_arguments(In, Name, ArgsIn),
    expand_prefix_list(ArgsIn, M, ArgsOut),
    compound_name_arguments(Out, Name, ArgsOut).
expand_prefixes(Term, _, Term).

expand_prefix_list([], _, []).
expand_prefix_list([H0|T0], M, [H|T]) :-
    expand_prefixes(H0, M, H),
    expand_prefix_list(T0, M, T).


% ----------------------------------------------------
% Goal-based queries
% These get translated into phrase-based queries.

%% query_goal(+EP,+Goal:sparql_goal,+Opts) is nondet.
%% query_goal(-EP,+Goal:sparql_goal,+Opts) is nondet.
%
%  Runs a SPARQL query against one or more SPARLQ endpoints.
%  Goal is converted into a textual SPARQL query using the DCG
%  defined in sparql_dcg.pl.
%
%  If EP is ground on entry, the query is run against the specified endpoint.
%  If EP is unbound on entry, the query is run agains all endpoints
%  in parallel, possibly returning multiple results from each.
%
%  (The following applies only to queries that return bindings, not
%  to simple boolean questions, which return only true or false.)
%  Options are as follows:
%     *  limit(L:natural)
%        At-most this many bindings will be returned per SPARQL call.
%     *  offset(O:natural)
%        Begin returning bindings from the Oth result on.
%     *  autopage(Auto:bool)
%        If false, a single SPARQL call is made using any limit and offset
%        options if supplied. If true, the the offset option is ignored
%        and multiple SPARQL queries are made as necessary to supply
%        results, using the limit option to determine the number of results
%        retrieved from the endpoint at a time.
%  Other options are passed to phrase_to_sparql/2.

:- meta_predicate parallel_query(2,+,-).

query_goal(EP,Goal,Opts) :-
   findall(QEP,endpoint(EP, QEP),EPs),
   EP=M:_,
   expand_prefixes(Goal,M,Goal1),
   term_variables(Goal1,Vars),
   (  Vars = [] % if no variables, do an ASK query, otherwise, SELECT
   -> phrase_to_sparql(ask(Goal),SPARQL),
      parallel_query(simple_query(SPARQL),EPs,EP-true)
   ;  Result =.. [row|Vars],
      setting(limit,DefaultLimit),
      select_option(limit(Limit),Opts,Opts1,DefaultLimit),
      (	  select_option(autopage(true),Opts1,Opts2)
      ->  phrase_to_sparql(select(Vars,Goal1,Opts2),SPARQL),
	  parallel_query(autopage_query(Limit,SPARQL),EPs,EP-Result)
      ;	  phrase_to_sparql(select(Vars,Goal1,Opts1),SPARQL),
	  parallel_query(simple_query(SPARQL),EPs,EP-Result)
      )
   ).

endpoint(M0:EP, M:EP) :-
    default_module(M0,M),
    current_predicate(M:sparql_endpoint/5),
    M:sparql_endpoint(EP,_,_,_,_).

simple_query(SPARQL,EP,EP-Result) :- query_sparql(EP,SPARQL,Result).
autopage_query(Limit,SPARQL,EP,EP-Result) :- autopage(EP,SPARQL,Limit,0,Result).

autopage(EP,SPARQL,Limit,Offset,Result) :-
   format(string(Q),'~s LIMIT ~d OFFSET ~d',[SPARQL,Limit,Offset]),
   findall(R,query_sparql(EP,Q,R),Results),
   (  member(Result,Results)
   ;  length(Results,Limit),     % no next page if length(Results) < Limit
      Offset1 is Offset + Limit, % next batch of results
      autopage(EP,SPARQL,Limit,Offset1,Result)
   ).

parallel_query(_,[],_) :- !, fail.
parallel_query(P,[X],Y) :- !, call(P,X,Y).
parallel_query(P,Xs,Y) :-
   maplist(par_goal(P,Y),Xs,Goals),
   concurrent_or(Y,Goals,[on_error(continue)]).

par_goal(P,Y,X,call(P,X,Y)).



%% query_phrase(+EP,+Q:sparqle_phrase(R),R) is nondet.
%% query_phrase(-EP,+Q:sparqle_phrase(R),R) is nondet.
%
% Phrase-based queries using the DCG defined in sparql_dcg.pl.
% The return type depends on the query:
% ==
% select(V:list(var), sparql_goal, options) :: sparql_phrase(row(N)) :- length(V,N).
% describe(resource,sparql_goal)            :: sparql_phrase(rdf).
% describe(resource)                        :: sparql_phrase(rdf).
% ask(sparql_goal)                          :: sparql_phrase(bool).
%
% rdf  ---> rdf(resource,resource,object).
% bool ---> true; false.
% ==
% =|row(N)|= is the type of terms of functor row/N.

query_phrase(EP,Phrase,Result) :-
   EP=M:_,
   expand_prefixes(Phrase,M,Phrase1),
   phrase_to_sparql(Phrase1,SPARQL),
   query_sparql(EP,SPARQL,Result).


phrase_to_sparql(Phrase,SPARQL) :-
   term_variables(Phrase,Vars),
   copy_term(t(Vars,Phrase),t(Vars1,Phrase1)),
   numbervars(Vars1,0,_),
   (  phrase(Phrase1,Codes) -> true
   ;  throw(unrecognised_query(Phrase))
   ),
   string_codes(SPARQL,Codes),
   debug(sparkle,'SPARQL query: ~s',[SPARQL]).

% ----------------------------------------------------
% In the end, everything comes through this.

%% query_sparql(?EP,SPARQL,-Result) is nondet.
%
%  Runs textual SPARQL query against an endpoint, exactly as
%  with sparql_query/3. If EP is unbound on entry, all known
%  endpoints will be tried sequentially.
query_sparql(EP,SPARQL,Result) :-
    endpoint(EP, Host,Port,Path,EPOpts),
    debug(sparkle,'Querying endpoint http://~w:~w~w',[Host,Port,Path]),
    sparql_query(SPARQL,Result,[host(Host),port(Port),path(Path)|EPOpts]).

endpoint(M0:EP, Host,Port,Path,EPOpts) :-
    default_module(M0,M),
    current_predicate(M:sparql_endpoint/5),
    M:sparql_endpoint(EP,Host,Port,Path,EPOpts).


		 /*******************************
		 *	  LOCAL SANDBOX		*
		 *******************************/

:- multifile
	sandbox:safe_primitive/1,
	sandbox:safe_meta/2,
	sandbox:safe_meta_predicate/1.

sandbox:safe_primitive(sparkle:endpoint(_,_)).
sandbox:safe_primitive(sparkle:endpoint(_,_,_,_,_)).
sandbox:safe_meta_predicate(sparkle:current_sparql_prefix/2).
sandbox:safe_meta(sparkle:parallel_query(P, _Xs, _Y), [Calls]) :-
	extend(P, [_,_], Calls).
sandbox:safe_meta(sparkle:phrase_to_sparql(Phr,_),[PhrEx]) :-
	extend(Phr, [_,_], PhrEx).
sandbox:safe_primitive(sparql_dcg:select(_,_,_,_,_)).
sandbox:safe_primitive(sparql_dcg:describe(_,_,_,_)).
sandbox:safe_primitive(sparql_dcg:describe(_,_,_)).
sandbox:safe_primitive(sparql_dcg:ask(_,_,_)).

extend(Var, _, _) :-
    var(Var), !,
    instantiation_error(Var).
extend(M:Term, Ex, M:TermEx) :- !,
    extend(Term, Ex, TermEx).
extend(Term, Ex, TermEx) :-
    Term =.. List,
    append(List, Ex, ListEx),
    TermEx =.. ListEx.


		 /*******************************
		 *	     MESSAGES		*
		 *******************************/

:- multifile prolog:message//1.

prolog:message(sparkle(Msg)) --> message(Msg).

message(updated_endpoint(EP, URL)) -->
    ['Updated SPARQL endpoint ~p to ~p'-[EP, URL]].

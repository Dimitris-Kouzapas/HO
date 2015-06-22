\documentclass{article}

\usepackage{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{url}
\usepackage{semantic}
\usepackage{stmaryrd}
\usepackage{xypic}
\usepackage{hyperref}
\usepackage{subfigure}
\usepackage{graphics}
\usepackage{color}
\usepackage{xy}
\xyoption{all}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%options ghci-7.8.2


%format tt = "\,`\!"

\newcommand{\dnote}[1]{\textcolor{blue}{Dom: #1}}

\begin{document}

\paragraph{Instructions}

\begin{itemize}
\item \textbf{Run this file in Haskell}: Go the command line and do
\texttt{ghci conchask.lhs} - you can then interact with the examples. For example:
%
\begin{verbatim}
$ ghci conchask.lhs
GHCi, version 7.10.1: http://www.haskell.org/ghc/  :? for help
[1 of 1] Compiling Main             ( conchask.lhs, interpreted )
Ok, modules loaded: Main.
*Main> run process5
Ping
Pong
*Main> :t client5
client5
  :: Channel ('Ch 'C)
     -> Channel ('Ch 'X)
     -> Session `['Ch 'C :-> (Ping :! End), 'Ch 'X :-> (Pong :! End)] ()
\end{verbatim}

\item \textbf{Compile the LaTeX version of this file to pdf}: From the command line
run \texttt{make}. This will generate \emph{conchask.pdf}. But you will need Haskell
and lhs2TeX installed. If you have Haskell installed, you can then install lhs2TeX easily with:
%%
\begin{verbatim}
cabal update
cabal install lhs2TeX
\end{verbatim}
%%
\end{itemize}

\section{Overview of the effect-system based encoding of 
the session-typed $HO\pi$-calculus into Haskell}

%if False

> {-# LANGUAGE RebindableSyntax, TypeOperators, DataKinds, KindSignatures, PolyKinds, TypeFamilies, ConstraintKinds, NoMonomorphismRestriction, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveDataTypeable, StandaloneDeriving, ExistentialQuantification, RankNTypes, UndecidableInstances, EmptyDataDecls, ScopedTypeVariables, GADTs, InstanceSigs, ImplicitParams #-}

> module Main where

> import Control.Concurrent ( threadDelay )
> import qualified Control.Concurrent.Chan as C
> import qualified Control.Concurrent as Conc

> import Data.Binary
> import Data.Typeable

> import qualified Prelude as P
> import Prelude hiding (Monad(..),print)

> import Control.Effect.Monad
> import Control.Effect 
> import GHC.TypeLits
> import Unsafe.Coerce
> import GHC.Prim

> import Data.Type.Set hiding (X, Y, Z, (:->), Nub, Union)

> ifThenElse True e1 e2 = e1
> ifThenElse False e1 e2 = e2

%endif

The basis of the $HO\pi$ encoding in Haskell is a \emph{graded monad}
which is used to track session information. This is encoded via the data type:

> data Session (s :: [*]) a = Session {getProcess :: IO a}

This wraps the |IO| monad in a binary type constructor |Session| with deconstructor
|getProcess :: Session s a -> IO a| and with a tag |s| used for type-level session information.
In practise, we only need |getProcess| internally, so this can be hidden. 
We define a type-refined version of |getProcess| which allows us to run a computation
only when the session environment is empty, that is, the process is closed with
respect to channels.

> run :: Session '[] a -> IO a
> run = getProcess

We can therefore run any session which will evaluate everything inside
of the |IO| monad and actually performing the communication/spawning/etc.

%if False

> instance Effect Session where
>    type Plus Session s t = UnionS s t
>    type Unit Session     = '[]
>    type Inv Session s t  = ()

>    return :: a -> Session (Unit Session) a
>    return a = Session (P.return a)

>    (>>=) :: (Inv Session s t) => Session s a -> (a -> Session t b) -> Session (Plus Session s t) b
>    (Session x) >>= k = Session ((P.>>=) x (getProcess . k))

> print :: Show a => a -> Session '[] ()
> print = liftIO . (P.print)

> liftIO :: IO a -> Session '[] a
> liftIO = Session 

-- Type-level machinery for composing session information

> type UnionS s t = Nub (Sort (Append s t))

> type family Nub t where
>    Nub '[]           = '[]
>    Nub '[e]          = '[e]
>    Nub ((c :-> s) ': (c :-> t) ': ss) = Nub ((c :-> (SessionPlus s t)) ': ss)
>    Nub (e ': f ': s) = e ': Nub (f ': s)

> type instance Cmp ((Ch c) :-> a) ((Op d) :-> b) = LT
> type instance Cmp ((Op c) :-> a) ((Ch d) :-> b) = GT
> type instance Cmp ((Ch c) :-> a) ((Ch d) :-> b) = CmpChan c d
> type instance Cmp ((Op c) :-> a) ((Op d) :-> b) = CmpChan c d

> type family CmpChan c d where
>             CmpChan c c = EQ
>             CmpChan C d = LT
>             CmpChan d C = GT
>             CmpChan d Z = LT
>             CmpChan Z d = GT
>             CmpChan D X = LT
>             CmpChan D Y = LT
>             CmpChan X Y = LT
>             CmpChan X D = GT
>             CmpChan Y D = GT
>             CmpChan Y X = GT

> type family SessionPlus s t where
>             SessionPlus End s = s
>             SessionPlus (t :? s) s' = t :? (SessionPlus s s')
>             SessionPlus (t :! s) s' = t :! (SessionPlus s s')
>             SessionPlus (Sel Left s t) s' = Sel Left (SessionPlus s s') t
>             SessionPlus (Sel Right s t) s' = Sel Right s (SessionPlus t s')
>             SessionPlus (s :& t) End  = (s :& t)
>             -- probably bogus
>             --SessionPlus (Sel Sup s t) s' = Sel Sup (SessionPlus s s') (SessionPlus t s')


%endif


Type-level session information will take the form of a list of mappings from
channel names to session types, written like: |'[c :-> S, d :-> T, ...]|.
This list will get treated as a set when we compose computations together, that is
there are no duplicate mappings of some channel variable |c|, and the ordering
will be normalise (this is a minor point and shouldn't affect too much here).

Session types are defined by the following type constructors: 

> -- Session types
> data a :! s
> data a :? s
> data End

Duality of session type is then defined as a simple type-level function:

> type family Dual s where
>     Dual End = End
>     Dual (t :! s) = t :? (Dual s)
>     Dual (t :? s) = t :! (Dual s)
>     Dual (Sel l s t) = (Dual s) :& (Dual t)
>     Dual (s1 :& s2) = Sel Sup (Dual s1) (Dual s2)

We define a (finite) set of channel name symbols |ChanNameSymbol|. 

> data ChanNameSymbol = X | Y | Z | C | D | ForAll -- reserved
> data ChanName = Ch ChanNameSymbol | Op ChanNameSymbol

|ChanName| thus can describe the dual end of a channel with |Op|. 
These are just names for channels. Channels themselves comprise an 
encapsulated Concurrent Haskell channel [todo: convert to a Cloud Haskell channel]

> data Channel (n :: ChanName) = forall a . Channel (C.Chan a) 


%if False

> infixl 2 :->
> data (k :: ChanName) :-> (v :: *)

%endif

\subsection{$\pi$-calculus part}

We can now define the core primitives for send and receive, which have types:

> send :: Channel c -> t -> Session '[c :-> t :! End] ()

\vspace{-2.3em}
%if False

> send (Channel c) t = Session (C.writeChan (unsafeCoerce c) t)

%endif

> recv :: Channel c -> Session '[c :-> t :? End] t

%if False

> recv (Channel c) = Session (C.readChan (unsafeCoerce c))

%endif

These both take a named channel |Channel c| and return a |Session| computation
indexed by the session environment |'[c :-> S]| where |S| is either a send
or receive action (terminated by |End|). These can then be composed using
the |do|-notation, which sequentially composes sesssion information.
For example:

> data Ping = Ping deriving Show
> data Pong = Pong deriving Show
>
> foo (c :: Channel (Ch C)) =  do  send c Ping
>                                  x <- recv c
>                                  return ((x + 1)::Int)

\noindent
This function is of type:
%
\begin{equation*}
|foo :: Channel (Ch C) -> Session '[Ch C :-> (Ping :! (Int :? End))] Int|
\end{equation*}
%
describing the session channel behaviour for |C|. 

I've given an explicit name to the channel |c| here via a type
signature, which names it as |Ch C|. This isn't strictly necessary
here, but it leads to a huge simplification in the inferred type.

The |new| combinator then models $\nu$,  which takes
a function mapping from a pair of two channels names
|Ch c| and |Op C| to a session with behaviour |s|, and creates
a session where any mention to |Ch c| or |Op c| is removed:

> new :: (Duality s c) => 
>               ((Channel (Ch c), Channel (Op c)) -> Session s b) 
>           ->  Session (Del (Del s (Op c)) (Ch c)) b

That is, the channels |Ch c| and |Op c| are only in scope for |Session s b|.

%if False

> new f = Session $ ((P.>>=) C.newChan (\c -> getProcess $ f (Channel c, Channel c)))

> type family Del (s :: [*]) (c :: ChanName) :: [*] where
>     Del '[]               c = '[]
>     Del ((c :-> s) ': xs) c = Del xs c
>     Del (x ': xs)         c = x ': (Del xs c)
>
> type family Lookup s c where
>             Lookup '[] c               = End 
>             Lookup ((c :-> t) ': xs) c = t
>             Lookup (x ': xs)     c     = Lookup xs c

%endif

The |Duality| predicate asks whether the session environment |s| contains
dual session types for channel |Ch C| and its dual |Op c|. 

%if False

> type family  Duality s c :: Constraint where
>              Duality s c = (Dual (Lookup s (Ch c))) ~ (Lookup s (Op c))

Here |Lookup s c| projects the session information for channel |c| out of the environment |s|,
and |~| is the type equality predicate. 

%endif

The session type encoding here is for an asynchronous calculus. In which case, the following
is allowed:

> foo2 = new (\(c :: (Channel (Ch C)), c') -> do  Ping <- recv c'
>                                                 send c Ping
>                                                 return ())

To use channels properly, we need parallel composition. This is given by:

> par :: (Disjoint s t) => Session s () -> Session t () -> Session (UnionS s t) () 

%if False

> par x y = Session $ ((P.>>) (Conc.forkIO $ getProcess x) 
>                       ((P.>>) (Conc.forkIO $ getProcess y) (P.return ())))

> class Disjoint s t 
> instance Disjoint '[] xs
> instance Disjoint xs '[]
> instance (NotMember c ys ~ True, Disjoint xs ys) => Disjoint ((c :-> s) ': xs) ys

> type family NotMember (c :: ChanName) (s :: [*]) :: Bool where
>             NotMember c '[] = True
>             NotMember c ((c :-> s) ': xs) = False
>             NotMember c ((d :-> s) ': xs) = NotMember c xs

%endif

\noindent
The binary predicate |Disjoint| here checks that |s| and |t| do not contain any of the same
channels. |UnionS| takes the disjoint union of the two environments. 

We can now define a complete example with communication:

> server c = do  Ping <- recv c
>                print "Server: Got a ping"
>              
> process = new (\(c, c') -> par (send c Ping) (server c'))

Which we can run with |run process| getting |"Server: Got a ping"|.
Note that the types here are completely inferred, giving 
|process :: Session '[] ()|. 

\subsubsection{Delegation}

So far we have dealt with only first-order channels (in the sense that they
can pass only values and not other channels). We introduce a ``delegate'' type
to wrap the session types of channels being passed:

> data DelgS s

Channels can then be sent with |chSend| primitive:

> chSend :: Channel c -> Channel d -> Session '[c :-> (DelgS s) :! End, d :-> s] ()

i.e., we can send a channel |d| with session type |s| over |c|. 

%if False

> chSend (Channel c) t = Session (C.writeChan (unsafeCoerce c) t)

%endif

The dual of this is a little more subtle. Receiving a delegated channel is given
by combinator, which is not a straightforward monadic function, but takes a function
as an argument:

> chRecv ::      Channel c -> (Channel d -> Session s a) ->
>                  Session (UnionS '[c :-> (DelgS (Lookup s d)) :? (Lookup s c)] (Del s d)) a

%if False
                                                            
> chRecv (Channel c) f = Session ((P.>>=) (C.readChan (unsafeCoerce c)) (getProcess . f))

%endif

\noindent

Given a channel |c|, and a computation which binds channel |d| to produces behaviour
|c|, then this is provided by receiving |d| over |c|. Thus the resulting computation
is the union of |c| mapping to the session type of |d| in the session environment 
|s|, composed with the |s| but with |d| deleted (removed). 

Here is an example using delegation. Consider the following process |server2|
which receives a channel |d| on |c|, and then seds a ping on it:

> server2 c = chRecv c (\(d :: Channel (Ch D)) -> send d Ping)

(Note, I have had to include explicit types to give a concrete name to the channel |d|,
this is an unfortunate artefact of the current encoding, but not too bad from a theoretical
perspect).

The type of |server2| is inferred as:
%%
< server2  ::  Channel c
<          ->  Session '[c :-> (DelgS (Ping :! End) :? Lookup '['Ch 'D :-> (Ping :! End)] c)] ()|

We then define a client to interact with this that binds |d| (and its dual |d'|),
then sends |d| over |c| and waits to receive a ping on |d'|

> client2 (c :: Channel (Ch C)) = 
>        new (\(d :: (Channel (Ch D)), d') -> 
>                              do  chSend c d
>                                  Ping <- recv d'
>                                  print "Client: got a ping")

This has inferred type:
%%
< client2
<  ::  Dual s ~ (Ping :? End) =>
<      Channel ('Ch 'C) -> Session '['Ch 'C :-> (DelgS s :! End)] ()

The type constraint says that the dual of |s| is a session that receives a |Ping|, 
so |s| is |Ping :! End|. 

We then compose |server2| and |client2| in parallel, binding the
channels |c| and its dual |c'| to give to client and server.

> process2 = new (\(c, c') -> par (client2 c) (server2 c'))

This type checks and can be then run (|run process2|) yielding |"Client: got a ping"|.

\subsection{Branching and choice}

To encode branching and choice, we introduce binary branch/select (from which
more complicated branch/select can be encoded) with two labels:

> data Left
> data Right
> data Sup 

> data Label l where
>        LeftL :: String -> Label Left
>        RightL :: String -> Label Right

The label data constructors |LeftL| and |RightL| also take string parameters for
convenience (to act as comments in the code). 

Note that whilst 'Sup' is a viable type-level label, there is no way to construct a label
value with this type index. This is used for subtyping, where |Sup| represents a selection
type which is a supertype. 

Selection and branching session types are provided by the following two type
constructors respectively: 

> data Sel l s t
> data s :& t

Select then has the type: 

> select :: Channel c -> Label l -> Session '[c :-> Sel l End End] ()

%if False

> select (Channel c) l = Session (C.writeChan (unsafeCoerce c) l)

%endif

The idea is that, given a channel |c|, and a label |l|, then a session 
is created with a select session type for label |l|. Any computations that 
get composed after that use |c| will add their session types into branch corresponding
to the label. For example:

> foo3 (c :: (Channel (Ch C))) = 
>          do  select c (LeftL "l")
>              v <- recv c
>              send c (42::Int)

|foo3| has the inferred type: 

< foo3 :: Channel ('Ch 'C)
<     -> Session '['Ch 'C :-> Sel Left (t :? (Int :! End)) End] ()|

That is, we see that after selecting the left branch, then |c| is used to receive
some |t| and then send an |Int|. 

Branching then has the following type:

> branch ::  ((Del s1 c) ~ (Del s2 c)) => 
>              Channel c  -> (Label Left -> Session s1 a)
>                         -> (Label Right -> Session s2 a)
>                        -> Session (UnionS (Del s1 c) '[c :-> ((Lookup s1 c) :& (Lookup s2 c))]) a

%if False

> branch (Channel c) f g = Session $
>                            (P.>>=) (C.readChan (unsafeCoerce c))
>                              (\l -> case l of 
>                                       LeftL l -> getProcess $ f (LeftL l)
>                                       RightL l -> getProcess $ g (RightL l))

%endif

This is a bit more complicated. The first parameter is the channel over which
a choice is being offered. Then come two continuations, the process if the 
left branch is taken and the process if the right branch is taken. Each gives
a session environment |s1| and |s2| but apart from a session type for |c|, these
must be equal (shown by the constraint |(Del s1 c) ~ (Del s2 c)|. Finally, the returned
session is that of |(Del s1 c)| unioned with |c| mapping to the |(Lookup s1 c) :& (Lookup s2 c)|,
i.e., the branching pair of the session types for |c| in the left and right branches.

Here's an example:

> process7 = new  (\(c :: (Channel (Ch C)), c') -> 
>                   do { select c (LeftL ""); send c 42 }
>                     `par` branch c'  (\(LeftL "") -> do { v <- recv c'; print v })
>                                      (\(RightL "") -> do { return (); return () } ))
>               

Then |run process7| yields 42 as expected. 

In order to take super types on selections, we define the following coercions that 
use the axiom $\mathbf{end} <: S$ to introduce an arbtirary supertype for $\mathbf{end}$ 
on the left-hande side of a selection or right:

> selSupL :: Session '[c :-> Sel l s End] () -> Session '[c :-> Sel Sup s t] ()
> selSupL s = Session $ getProcess s
>
> selSupR :: Session '[c :-> Sel l End s] () -> Session '[c :-> Sel Sup t s] ()
> selSupR s = Session $ getProcess s               

These are useful in the hotel example.

\subsection{$\lambda$-part}

Since we are embedding the $HO\pi$-calculus, we can abstract over channels with
linear functions. So far we have defined functions which take particular names channels
as arguments, but we have not abstracted over channels names. We now introduce
linear functions which can abstract over channels (and the session types of those channels).

We abstract functions via a type constructor |Abs|

> data Abs t a where
>      Abs :: (Channel c -> Session s a) -> Abs (Lookup s c) a

The |Abs| data constructor should be considered as abstract [it can be hidden]. Instead,
we provide the follow constructor for (linear) abstractions: 

> absL :: (Channel c -> Session s a) -> Session (Del s c) (Abs (Lookup s c) a)
> absL f = Session (P.return $ Abs f)

The |absL| constructor takes a function of type |(Channel c -> Session
s a)|, that is, a function from some channel |c| to a |Session|
environment |s|. This returns a result |Session (Del s c) (Abs (Lookup s c) a)| which 
describes a function which takes some channel with session type |Lookup s c|, 
i.e., 
returns a result of type |a|, and is embedded in a session with
environment |Del s c|, cf. 

\begin{equation*}
\inference{\Delta, c : T \vdash C : \diamond}
          {\Delta \vdash \lambda c . C : T \multimap \diamond}
\end{equation*}

The main different here is that we can actual return a result (of type |a|), rather than just
being a process $\diamond$. \dnote{We need to decide whether we want to keep the ability for a value
to returns from an abstraction, but for the moment it makes the hotel example easier (see Section~\ref{sec:hotel}).}

These functions can then be applied by the following primitive:  

> appL :: Abs t a -> Channel c -> Session '[c :-> t] a

%if False 

> appL (Abs k) c = let (Session s) = k (unsafeCoerce c) in Session s

> 

%endif

Whatever concrete name was used for the channel in the abstracted process is replaced
by the channel name here.

Thus, given a linear session function |Abs t a| and some channel |c| then
we get a session with mapping |c :-> t|. 
Here's an example: a client abstract over a channel, and then applies it within
the same process:

> client4 (c :: Channel (Ch C)) = 
>             do  f <- absL (\c -> send c Ping)
>                 appL f c

This simply has type |client4 :: Channel ('Ch 'C) -> Session '['Ch 'C :-> (Ping :! End)] ()|.
We can then interfact with this in a usual straightforwad way.

> process4 = new (\(c, c') -> (client4 c) `par` (do {x <- recv c'; print x }))


A more complicated example creates a closure over an other channel |x|:

> client5 (c :: Channel (Ch C)) (x :: (Channel (Ch X))) = 
>    do  f <- absL  (\(c :: (Channel (Ch D))) -> do  send c Ping
>                                                    send x Pong)
>        appL f c 
>        -- appL f d  -- not allowed due to linearity... 

The type is inferred type as:

< client5  :: Channel ('Ch 'C)
<          -> Channel ('Ch 'X)
<          -> Session '['Ch 'C :-> (Ping :! End), 'Ch 'X :-> (Pong :! End)] ()
%
We can then interact with this process in the expected way: 

> process5 =  new (\(c :: Channel (Ch C), c') -> 
>                 new (\(x :: Channel (Ch X), x') ->
>                     (client5 c x) `par`
>                           do  v <- recv c'
>                               print v
>                               v <- recv x'
>                               print v))

Where |run process5| prints \texttt{Ping} then \texttt{Pong}. 
\dnote{TODO: should we also include a non-linear function application/abstraction for completeneess with
HO?}

Dimtris' example:

> client6 (c :: (Channel (Ch C))) (d :: (Channel (Ch D))) = 
>     do  f <- absL (\(z :: (Channel (Ch Z))) -> (send z 42 `par` send c 7))
>         appL f d

> process6 =  new (\(c :: (Channel (Ch C)), c') -> 
>               new (\(d :: (Channel (Ch D)), d') ->
>                     do  client6 c d
>                         v1 <- recv c' 
>                         v2 <- recv d'
>                         return (v1 + v2)))

|run process6| returns |49| as expected.


\section{Hotel booking scenario} 
\label{sec:hotel}

The $P_{xy}$ process is encoded using two layers of abstraction to abstract over $y$ and $x$ (in that order).
We use Haskell's implicit parameters feature to insert |room| and |credit| information, which are abstract
here. $P_{xy}$ is defined via |p|:

> p  =  absL (\(y :: (Channel (Ch Y))) -> 
>        absL (\(x :: (Channel (Ch X))) -> 
>               do  send x  (?room)
>                   quote <- recv x
>                   send y quote
>                   branch y  (\(LeftL "accept") -> selSupL $ do  select x (LeftL "accept")
>                                                                 send x  (?credit))
>                             (\(RightL "reject") -> selSupR $ select x (RightL "reject"))))

 
[Don't let the question marks ? here confused, they are nothing to do with sending, this just marks
them as 'dynamic'/implicit parameters for Haskell] This has its type inferred as:

< p :: (?room :: String, ?credit :: Int) => 
<        Session '[]  (Abs (Int :! (End :& End)) 
<                         (Abs (String :! (Int :? (Sel Sup (Int :! End) End))) ()))

The client is then: 

> client (s1 :: (Channel (Ch Y))) (s2 :: (Channel (Ch Z))) =
>             new (\(h1 :: (Channel (Ch C)), h1') ->
>             new (\(h2 :: (Channel (Ch D)), h2') -> 
>                (do  p0 <- p 
>                     p1 <- p  
>                     ph1 <- appL p0 h1  -- implements $\lambda x . P_{x,y} \{h1/y\}$
>                     ph2 <- appL p1 h2  -- implements $\lambda x . P_{x,y} \{h2/y\}$
>                     send s1 ph1 
>                     send s2 ph2)
>            `par` (do  x <- recv h1'
>                       y <- recv h2'
>                       if (x <= y)  then do  selSupL (select h1' (LeftL "accept"))
>                                             selSupR (select h2' (RightL "reject"))
>                                    else do  selSupR (select h1' (RightL "reject"))
>                                             selSupL (select h2' (LeftL "acccept")))))

Which has its type inferred as:

< client
<  :: (?credit::Int, ?room::String) =>
<        Channel ('Ch 'Y)
<     -> Channel ('Ch 'Z)
<     -> Session
<          '['Ch 'Y
<            :-> (Abs (String :! (Int :? Sel Sup (Int :! End) End)) () :! End),
<            'Ch 'Z
<            :-> (Abs (String :! (Int :? Sel Sup (Int :! End) End)) () :! End)]
<          ()
 
This is equivalent to the session typing for |client|:

\begin{equation*}
\begin{array}{l}
y : ![ \; (![\textbf{String}]. ?[\textbf{Int}] . \oplus[\mathsf{accept} : ![\textbf{Int}], \mathsf{reject} : \mathbf{end}]) \multimap \diamond], \\
z : ![ \; (![\textbf{String}]. ?[\textbf{Int}] . \oplus[\mathsf{accept} : ![\textbf{Int}], \mathsf{reject} : \mathbf{end}]) \multimap \diamond]
\end{array} \vdash \emph{client}
\end{equation*}

\section{Typed encoding - HO$\pi$ to HO}

\subsection{Derivability of typing}

> sendD :: Channel c -> t -> Session g b -> Session (UnionS '[c :-> t :! End] g) b
> sendD c v p = send c v >>= (\() -> p)

> {-
> sendConv
>  :: Channel (Ch X)
>     -> Channel (Ch Y)
>     -> Session '[Ch X :-> (Abs (Abs t a :? End) a :! End), Ch Y :-> t] ()

> sendConv u w =   do f <- absL  
>                            (\(z :: (Channel (Ch Z))) -> do x <- recv z
>                                                            appL x w)
>                     send u f
> -}





\end{document}
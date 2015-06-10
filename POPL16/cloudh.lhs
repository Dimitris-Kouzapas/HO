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
%format :~> = ":\leadsto"

\newcommand{\dnote}[1]{\textcolor{blue}{Dom: #1}}

\begin{document}

\section{A brief overview of the effect-system based encoding of 
the session-typed $\pi$+$\lambda$-calculus into Haskell}

%if False

> {-# LANGUAGE RebindableSyntax, TypeOperators, DataKinds, KindSignatures, PolyKinds, TypeFamilies, ConstraintKinds, NoMonomorphismRestriction, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, DeriveDataTypeable, StandaloneDeriving, ExistentialQuantification, RankNTypes, UndecidableInstances, EmptyDataDecls, ScopedTypeVariables, GADTs, InstanceSigs #-}

> module Main where

> import Control.Concurrent ( threadDelay )
> import qualified Control.Concurrent.Chan as C
> import qualified Control.Concurrent as Conc

> import Data.Binary
> import Data.Proxy
> import Data.Typeable

> import qualified Prelude as P
> import Prelude hiding (Monad(..),print)

> import Control.Effect.Monad
> import Control.Effect 
> import GHC.TypeLits
> import Unsafe.Coerce
> import GHC.Prim

> import Data.Type.Set hiding (X, Y, Z, (:->), Nub, Union)

%endif

The basis of the $\pi+\lambda$ encoding in Haskell is a \emph{graded monad}
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
>    type Inv Session s t  = (NoDualNames s t ~ NoSeqDuals)

>    return :: a -> Session (Unit Session) a
>    return a = Session (P.return a)

>    (>>=) :: (Inv Session s t) => Session s a -> (a -> Session t b) -> Session (Plus Session s t) b
>    (Session x) >>= k = Session ((P.>>=) x (getProcess . k))

> print :: Show a => a -> Session '[] ()
> print = liftIO . (P.print)

> liftIO :: IO a -> Session '[] a
> liftIO = Session 

-- Type-level machinery for composing session information

> data DualCon = NoSeqDuals | DualConflict ChanName

> type family NoDualNames s t :: DualCon where
>             NoDualNames '[] s  = NoSeqDuals
>             NoDualNames s '[]  = NoSeqDuals
>             NoDualNames ((c :-> s) ': ss) ts = And (NonDualNames' c ts) (NoDualNames ss ts)
>             NoDualNames ((c :~> s) ': ss) ts = NoDualNames ss ts

> type family NonDualNames' c t :: DualCon where
>             NonDualNames' c '[] = NoSeqDuals
>             NonDualNames' (Ch c) (((Op c) :-> s) ': ss) = DualConflict (Ch c)
>             NonDualNames' (Op c) (((Ch c) :-> s) ': ss) = DualConflict (Op c)
>             NonDualNames' c ((d :-> s) ': ss) = NonDualNames' c ss
>             NonDualNames' c ((d :~> s) ': ss) = NonDualNames' c ss
>
> type family And (s :: DualCon) (t :: DualCon) :: DualCon where
>             And (DualConflict c) x = DualConflict c
>             And x (DualConflict c) = DualConflict c
>             And NoSeqDuals NoSeqDuals = NoSeqDuals

> type UnionS s t = Nub (Sort (Append s t))

> type family Nub t where
>    Nub '[]           = '[]
>    Nub '[e]          = '[e]
>    Nub ((c :-> s) ': (c :-> t) ': ss) = Nub ((c :-> (SessionPlus s t)) ': ss)
>    Nub ((c :~> s) ': (c :~> t) ': ss) = Nub ((c :~> (SessionPlus s t)) ': ss) 
>    Nub (e ': f ': s) = e ': Nub (f ': s)

> type instance Cmp ((Ch c) :-> a) ((Op d) :-> b) = LT
> type instance Cmp ((Op c) :-> a) ((Ch d) :-> b) = GT
> type instance Cmp ((Ch c) :-> a) ((Ch d) :-> b) = CmpChan c d
> type instance Cmp ((Op c) :-> a) ((Op d) :-> b) = CmpChan c d

All repeats, but deal with :~> 

> type instance Cmp ((Ch c) :~> a) ((Op d) :~> b) = LT
> type instance Cmp ((Op c) :~> a) ((Ch d) :~> b) = GT
> type instance Cmp ((Ch c) :~> a) ((Ch d) :~> b) = CmpChan c d
> type instance Cmp ((Op c) :~> a) ((Op d) :~> b) = CmpChan c d

> type instance Cmp ((Ch c) :~> a) ((Op d) :-> b) = LT
> type instance Cmp ((Op c) :~> a) ((Ch d) :-> b) = GT
> type instance Cmp ((Ch c) :~> a) ((Ch d) :-> b) = CmpChan c d
> type instance Cmp ((Op c) :~> a) ((Op d) :-> b) = CmpChan c d

> type instance Cmp ((Ch c) :-> a) ((Op d) :~> b) = LT
> type instance Cmp ((Op c) :-> a) ((Ch d) :~> b) = GT
> type instance Cmp ((Ch c) :-> a) ((Ch d) :~> b) = CmpChan c d
> type instance Cmp ((Op c) :-> a) ((Op d) :~> b) = CmpChan c d

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

We define a (finite) set of channel name symbols |ChanNameSymbol|
[this can be generalised away, but for some slightly subtle reasons
mostly to do with CloudHaskell internals I have avoided the
generalisation for the moment].

> data ChanNameSymbol = X | Y | Z | C | D 
> data ChanName = Ch ChanNameSymbol | Op ChanNameSymbol

|ChanName| thus can describe the dual end of a channel with |Op|. 
These are just names for channels. Channels themselves comprise an 
encapsulated Concurrent Haskell channel [todo: convert to a Cloud Haskell channel]

> data Channel (n :: ChanName) = forall a . Channel (C.Chan a) deriving Typeable


%if False

> infixl 2 :->
> data (k :: ChanName) :-> (v :: *)

> infixl 2 :~>
> data (k :: ChanName) :~> (v :: *)

%endif

\subsection{$\pi$-calculus part}

We can now define the core primitives for send and receive, which have types:

> send :: Channel c -> t -> Session '[c :-> t :! End] ()

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
>           ->  Session (Del (Ch c) (Del (Op c) s)) b

That is, the channels |Ch c| and |Op c| are only in scope for |Session s b|.

%if False

> new f = Session $ ((P.>>=) C.newChan (\c -> getProcess $ f (Channel c, Channel c)))

> type family Del (c :: ChanName) (s :: [*]) :: [*] where
>     Del c '[]           = '[]
>     Del c ((c :-> s) ': xs) = Del c xs
>     Del c ((c :~> s) ': xs) = Del c xs
>     Del c (x ': xs)     = x ': (Del c xs)
>
> type family Lookup s c where
>             Lookup '[] c               = End 
>             Lookup ((c :-> t) ': xs) c = t
>             Lookup ((c :~> t) ': xs) c = t
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

The effect monad used to sequence session information also has some predicates
to check that dual session channels do not appear in the same (sequential) session.
For example, the following is a type error: 

\begin{code}% This code fails to type check
foo2a = new (\(c :: (Channel (Ch C)), c' :: (Channel (Op C))) -> 
                  do Ping <- recv c'
                     send c Ping
                     return ())
\end{code}% this is not really code

The produces a type error: 
%%
\begin{verbatim}
cloudh.lhs:283:23:
    Couldn't match type `'DualConflict ('Op 'C)' with `'NoSeqDuals'
    In a stmt of a 'do' block: Ping <- recv c'
......
\end{verbatim}
%%

(In the case of delegation, this check is not used, so delegated channels
can appear in sequential composition with their dual channel names- this is 
an interesting subtlety that requires a bit of extra work in the background. It is
not seen at the top-level though).

To use channels properly, we need parallel composition. This is given by:

> par :: (Disjoint s t) => Session s () -> Session t () -> Session (UnionS s t) () 

%if False

> par x y = Session $ ((P.>>) (Conc.forkIO $ getProcess x) 
>                       ((P.>>) (Conc.forkIO $ getProcess y) (P.return ())))

> {- spawnLocal x
>              spawnLocal y
>                where spawnLocal :: Session s () -> Session s ()
>                      spawnLocal (Session p) = Session $ (P.>>) (Conc.forkIO p) (P.return ()) -}

> class Disjoint s t 
> instance Disjoint '[] xs
> instance Disjoint xs '[]
> instance (NotMember c ys ~ True, Disjoint xs ys) => Disjoint ((c :-> s) ': xs) ys

> type family NotMember (c :: ChanName) (s :: [*]) :: Bool where
>             NotMember c '[] = True
>             NotMember c ((c :-> s) ': xs) = False
>             NotMember c ((c :~> s) ': xs) = False
>             NotMember c ((d :-> s) ': xs) = NotMember c xs
>             NotMember c ((d :~> s) ': xs) = NotMember c xs

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

> chSend :: Channel c -> Channel d -> Session '[c :-> (DelgS s) :! End, d :~> s] ()

i.e., we can send a channel |d| with session type |s| over |c|. 

[Note, the different mapping |:~>| instead of |:->| for |d|, this marks to the type system
that this channel has been delegated, therefore it can appear in the same environment
as the dual channel of |d|.]

%if False

> chSend (Channel c) t = Session (C.writeChan (unsafeCoerce c) t)

%endif

The dual of this is a little more subtle. Receiving a delegated channel is given
by combinator, which is not a straightforward monadic function, but takes a function
as an argument:

> chRecv ::      Channel c -> (Channel d -> Session s a) ->
>                  Session (UnionS '[c :-> (DelgS (Lookup s d)) :? (Lookup s c)] (Del d s)) a

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

> server2 c = chRecv c
>              (\(d :: Channel (Ch D)) -> send d Ping)

(Note, I have had to include explicit types to give a concrete name to the channel |d|,
this is an unfortunate artefact of the current encoding, but not too bad from a theoretical
perspect).

The type of |server2| is inferred as:
%%
\begin{equation*}
|server2  :: 
Channel c
     -> Session '[c :-> (DelgS (Ping :! End) :? Lookup '['Ch 'D :-> (Ping :! End)] c)] ()|
\end{equation*}

We then define a client to interact with this that binds |d| (and its dual |d'|),
then sends |d| over |c| and waits to receive a ping on |d'|

> client2 (c :: Channel (Ch C)) = 
>        new (\(d :: (Channel (Ch D)), d') -> 
>                              do chSend c d
>                                 Ping <- recv d'
>                                 print "Client: got a ping")

This has inferred type:
%%
\begin{equation*}
|client2
  :: Dual s ~ (Ping :? End) =>
     Channel ('Ch 'C) -> Session '['Ch 'C :-> (DelgS s :! End)] ()|
\end{equation*}
%%
The type constraint says that the dual of |s| is a session that receives a |Ping|, 
so |s| is |Ping :! End|. 

We then compose |server2| and |client2| in parallel, binding the
channels |c| and its dual |c'| to give to client and server.

> process2 = new (\(c, c') -> par (client2 c) (server2 c'))

This type checks and can be then run (|run process2|) yielding |"Client: got a ping"|.


\subsection{$\lambda$-part}

Since we are studying the $\pi+\lambda$-calculus, we can abstract over channels with
linear functions. So far we have abstracted over channels, but not in an \emph{operational
sense}- think of this more as let-binding style substitution (cut). We now introduce
linear functions which can abstract over channels (and the session types of those channels, 
which the previous form of abstraction above \textbf{doesn't do}, it just abstracts over 
names, not the session types associated with their names).

First, we abstract functions via a type constructor |Abs|

> data Abs t s = Abs (Proxy s) (forall c . (Channel c -> Session (UnionS s '[c :-> t]) ()))

The |Abs| data constructor takes a function of type |forall c
. (Channel c -> Session (UnionS s '[c :-> t]) ())|, that is, a
function from \emph{universally quanitifed} channel name |c| to a
|Session| environment |s| where |c :-> t| is a member). Since |UnionS|
is a non-injective function we also need a (trivial) type annotation
that explains exactly what is the remaining channel- this is |Proxy s|
(I'll shown an example in the moment).  This returns a result |Abs t s|
which describes a function which takes some channel with session type |t| and
has session environment |s|, cf.

\begin{equation*}
\inference{\Delta, c : T \vdash C : \Diamond}
          {\Delta \vdash \lambda c . C : T \multimap \Diamond}
\end{equation*}

This can then be applied by the following primitive 

> appH :: Abs t s -> Channel c -> Session (UnionS s '[c :-> t]) ()
> appH (Abs _ k) c = k c


Thus, given a linear session function |Abs t s| and some channel |c| then
we get a session with environment |s| and a mapping |c :-> t|. 
Here's an example: a client abstract over a channel, and then applies it within
the same process:

> client4 (c :: Channel (Ch C)) = do 
>                let f = Abs (Proxy :: (Proxy '[])) (\c -> send c Ping)
>                appH f c

This simply has type |client4 :: Channel ('Ch 'C) -> Session '['Ch 'C :-> (Ping :! End)] ()|.
We can then interfact with this in a usual straightforwad way.

> process4 = new (\(c, c') -> (client4 c) `par` (do {x <- recv c'; print x }))


\end{document}
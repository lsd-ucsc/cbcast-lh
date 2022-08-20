---
geometry: margin=2cm
header-includes: |
    \usepackage{amssymb}
    \usepackage{bussproofs}
...

# Network semantics for CBCAST

Taking inspiration from Fig 6 in verdi, we specialize those two rules to obtain
ones that we can actually implement in LH.

Give shorter names to the transitions in our CBCAST implementation.

```haskell
  import CBCAST.Core
  import CBCAST.Transitions
  
  send = internalBroadcast :: r -> Process r -> (Message r, Process r)
  recv = internalReceive :: Message r -> Process r -> Process r
  dlvr = internalDeliver :: Process r -> Maybe (Message r, Process r)
```

Take the Fig 6 **Input** rule from verdi and split it into two rules for the
things that a process does independently of the network: Sending messages and
delivering messages.
This means that instead of $H_{\text{inp}}$, we directly apply $\Sigma[n]$ to
`send` or `dlvr` to obtain $\sigma'$ and also construct $P'$ manually.
Additionally, remove the $T$ (trace) part of the state tuple because we don't
need it.

\begin{prooftree}
    \AxiomC{$
        (m, \sigma') = \texttt{send}(r, \Sigma[n])
    $}
    \AxiomC{$
        P' = \{ (n, dst, m) \; | \; \forall \; dst:\text{PID}. \; n \neq dst \}
    $}
    \AxiomC{$
        \Sigma' = \Sigma[n\mapsto \sigma']
    $}
    \TrinaryInfC{$
        (P, \Sigma)
        \rightsquigarrow
        (P \uplus P', \Sigma')
    $}
    [send]
\end{prooftree}

> Notes about this send rule: $n$ is the PID of a process in the execution
$\Sigma$, and $r$ is a client-application message value. $P'$ addresses packets
to each PID distinct from $n$. Elided from this inference rule is the
client-application of our library applying $m$ to itself to update its
state.^[The send rule could be simplified by addressing packets to all PIDs.
Then the client-application doesn't need to apply $m$ to itself in the send
rule. This wouldn't reflect our implementation, however, which seeks to keep
the network out of the fast-path between client-application and self-sent
messages.]

\begin{prooftree}
    \AxiomC{$
        \texttt{Just} \; (m, \sigma') = \texttt{dlvr}(\Sigma[n])
    $}
    \AxiomC{$
        \Sigma' = \Sigma[n\mapsto \sigma']
    $}
    \BinaryInfC{$
        (P, \Sigma)
        \rightsquigarrow
        (P, \Sigma')
    $}
    [deliver]
\end{prooftree}

> Notes about this deliver rule: $n$ is the PID of a process in the execution
$\Sigma$. No packets are sent. Elided from this inference rule is the
client-application of our library applying $m$ to itself to update its
state.^[If we wanted to include applying $m$ in the inference rule, here are
some approaches:
(1) Change $\Sigma$'s type from $\text{PID} \rightarrow \texttt{Process r}$ to
$\text{PID} \rightarrow (\text{app-state}, \texttt{Process r})$ for some
client-application state type.
(2) Change the state tuple to include (in addition to $\Sigma : \text{PID}
\rightarrow \texttt{Process r}$) something of type $\text{PID} \rightarrow
\text{app-state}$ for some client-application state type.]

Take the Fig 6 **Deliver** rule from verdi for reading a packet (message) from
the network (which is called receiving in CBCAST).
Instead of $H_{\text{net}}$, we directly apply $\Sigma[n]$ to `recv` to obtain
$\sigma'$.

\begin{prooftree}
    \AxiomC{$
        \sigma' = \texttt{recv}(m, \Sigma[dst])
    $}
    \AxiomC{$
        \Sigma' = \Sigma[dst\mapsto \sigma']
    $}
    \BinaryInfC{$
        ( \{ (src, dst, m) \} \uplus P, \Sigma)
        \rightsquigarrow
        ( P, \Sigma')
    $}
    [receive]
\end{prooftree}

> Notes about this receive rule: $dst$ is the PID of a process in the execution
$\Sigma$. No packets are sent.

A few more things, and then the final set of rules:

* Rename $n$ to $src$ in the send rule for consistency with the third rule.
* Instead of a "multiset-union operator" which can apparently pattern match to
  extract an arbitrary subset (see the third rule), we'll change
  $P:\text{MultiSet (\text{PID},\text{PID},m)}$ to
  $P:[(\text{PID},\text{PID},m)]$ and use list operators (append
  $\texttt{++}$ and cons $::$). We'll add a permutation rule to account for the
  arbitrarily chosen packet.

\begin{prooftree}
    \AxiomC{$
        (m, \sigma') = \texttt{send}(r, \Sigma[src])
    $}
    \AxiomC{$
        P' = [ (src, dst, m) \; | \; \forall \; dst:\text{PID}. \; src \neq dst ]
    $}
    \AxiomC{$
        \Sigma' = \Sigma[src \mapsto \sigma']
    $}
    \TrinaryInfC{$
        (P, \Sigma)
        \rightsquigarrow
        (P \texttt{++} P', \Sigma')
    $}
    [send]
\end{prooftree}

\begin{prooftree}
    \AxiomC{$
        \texttt{Just} \; (m, \sigma') = \texttt{dlvr}(\Sigma[n])
    $}
    \AxiomC{$
        \Sigma' = \Sigma[n \mapsto \sigma']
    $}
    \BinaryInfC{$
        (P, \Sigma)
        \rightsquigarrow
        (P, \Sigma')
    $}
    [deliver]
\end{prooftree}

\begin{prooftree}
    \AxiomC{$
        \sigma' = \texttt{recv}(m, \Sigma[dst])
    $}
    \AxiomC{$
        \Sigma' = \Sigma[dst \mapsto \sigma']
    $}
    \BinaryInfC{$
        ( (src, dst, m) :: P, \Sigma)
        \rightsquigarrow
        ( P, \Sigma')
    $}
    [receive]
\end{prooftree}

\begin{prooftree}
    \AxiomC{\texttt{isPermutationOf}(P, P')}
    \UnaryInfC{$
        ( P, \Sigma )
        \rightsquigarrow
        ( P', \Sigma )
    $}
    [permute]
\end{prooftree}

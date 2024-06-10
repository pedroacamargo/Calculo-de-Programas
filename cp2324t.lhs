\documentclass[11pt, a4paper, fleqn]{article}
\usepackage{cp2324t}
\makeindex

%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (lcbr3 (x)(y)(z)) = "\begin{lcbr}" x "\\" y "\\" z "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textbf{NB}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\llparenthesis\, " f "\,\rrparenthesis"
%format (cataNat (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataList (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataRose (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny R}"
%format (ana (g)) = "\ana{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format (anaLTree (g)) = "\lanabracket\," g "\,\ranabracket"
%format (anaRose (g)) = "\lanabracket\," g "\,\ranabracket_\textit{\tiny R}"
%format (hylo (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"
%format (hyloList (g) (h)) = "\hyloList{" g "}{" h "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format delta = "\Delta "
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!+}"
%format Integer  = "\mathbb{Z}"
%format (Cp.cond (p) (f) (g)) = "\mcond{" p "}{" f "}{" g "}"
%format (square (x)) = x "^2"

%format (cataTree (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny T}}"
%format (cataForest (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny F}}"
%format (anaTree (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny T}}"
%format (anaForest (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny F}}"
%format (hyloTree (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny T}}"
%format (hyloForest (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny F}}"
%format inTree = "\mathsf{in}_{Tree}"
%format inForest = "\mathsf{in}_{Forest}"
%format outTree = "\mathsf{out}_{Tree}"
%format outForest = "\mathsf{out}_{Forest}"

%format (cata' (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis"
%format (ana' (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket"
%format (hylo' (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket"
%------------------------------------------------------------------------------%


%====== DEFINIR GRUPO E ELEMENTOS =============================================%

\group{G19}
\studentA{102499}{Carlos Daniel Silva Fernandes}
\studentB{102497}{José Bernardo Moniz Fernandes}
\studentC{102504}{Pedro Augusto Camargo}

%==============================================================================%

\begin{document}
\sffamily
\setlength{\parindent}{0em}
\emergencystretch 3em
\renewcommand{\baselinestretch}{1.25} 
\input{Cover}
\pagestyle{pagestyle}

\newgeometry{left=25mm,right=20mm,top=25mm,bottom=25mm}
\setlength{\parindent}{1em}

\section*{Preâmbulo}

\CP\ tem como objectivo principal ensinar a progra\-mação de computadores
como uma disciplina científica. Para isso parte-se de um repertório de \emph{combinadores}
que formam uma álgebra da programação % (conjunto de leis universais e seus corolários)
e usam-se esses combinadores para construir programas \emph{composicionalmente},
isto é, agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell, sem prejuízo da sua aplicação a outras linguagens
funcionais. Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell. Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

Antes de abordarem os problemas propostos no trabalho, os grupos devem ler
com atenção o anexo \ref{sec:documentacao} onde encontrarão as instruções
relativas ao sofware a instalar, etc.

\begin{alert}
Valoriza-se a escrita de \emph{pouco} código, que corresponda a soluções
simples e elegantes mediante a utilização dos combinadores de ordem superior
estudados na disciplina.

Recomenda-se ainda que o código venha acompanhado de uma descrição de como
funciona e foi concebido, apoiado em diagramas explicativos. Para instruções
sobre como produzir esses diagramas e exprimir raciocínios de cálculo, ver
o anexo \ref{sec:diagramas}.
\end{alert}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac,chunksOf)
import Nat hiding (aux)
import LTree
import Exp
import Prob
import Probability hiding (D)
import Data.Char
import Data.List hiding (find)
import Data.Ord
import Data.List.Split  hiding (split)
-- import Svg hiding (for)
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
import RelCalc (hist)
-- import Control.Concurrent

main = undefined
\end{code}
%endif

\Problema

No passado dia 10 de Março o país foi a eleições para a Assembleia da República.
A lei eleitoral portuguesa segue, como as de muitos outros países, o chamado
\hondt{Método de Hondt} para selecionar os candidatos dos vários partidos, conforme
os votos que receberam. E, tal como em anos anteriores, há sempre 
\href{https://www.jn.pt/6761243323/mais-de-673-mil-votos-desperdicados-nas-legislativas}{notícias}
a referir a quantidade de votos desperdiçados por este método.
Como e porque é que isso acontece?

Pretende-se nesta questão construir em Hakell um programa que implemente
o método de Hondt. A \cne{Comissão Nacional de Eleições} descreve esse método
\hondt{nesta página}, que deverá
ser estudada para resolver esta questão. O quadro que aí aparece,

\qhondt

\noindent mostra o exemplo de um círculo eleitoral que tem direito a eleger 7 deputados e
onde concorrem às eleições quatro partidos |A|, |B|, |C| e |D|, cf:
\begin{code}
data Party = A | B | C | D deriving (Eq,Ord,Show)
\end{code}
A votação nesse círculo foi
\begin{spec}
[(A,12000),(B,7500),(C,4500),(D,3000)]
\end{spec}
sendo o resultado eleitoral
\begin{spec}
result = [(A,3),(B,2),(C,1),(D,1)]
\end{spec}
apurado correndo
\begin{code}
result = final history
\end{code}
que corresponde à última etapa da iteração:
\begin{code}
history =  [ for step db i | i <- [0..7] ]
\end{code}
Verifica-se que, de um total de |27000| votos, foram desperdiçados:
\begin{spec}
wasted =  9250
\end{spec}

Completem no anexo \ref{sec:resolucao} as funções que se encontram aí
indefinidas\footnote{Cf.\ |undefined| no código.}, podendo adicionar funções
au\-xiliares que sejam convenientes. No anexo \ref{sec:codigo} é dado
algum código preliminar.

\Problema

A biblioteca \LTree\ inclui o algoritmo ``mergesort'' (\msort{|mSort|}), que é um hilomorfismo
baseado função
\begin{spec}
merge :: Ord a => ([a], [a]) -> [a]
\end{spec}
que junta duas listas previamente ordenadas numa única lista ordenada.

Nesta questão pretendemos generalizar |merge| a |k|-listas (ordenadas),
para qualquer |k| finito:
\begin{code}
mergek :: Ord a => [[a]] -> [a]
\end{code}
Esta função deverá ser codificada como um hilomorfismo, a saber:
\begin{code}
mergek = hyloList f g 
\end{code}
\begin{enumerate}
\item	Programe os genes |f| e |g| do hilomorfismo |mergek|.
\item	Estenda |mSort| a
\begin{code}
mSortk :: Ord a => Int -> [a] -> [a]
\end{code}
por forma a este hilomorfismo utilizar |mergek| em lugar de |merge| na estapa
de ``conquista". O que se espera de |mSortk k| é que faça a partição da lista
de entrada em |k| sublistas, sempre que isso for possível.
(Que vantagens vê nesta nova versão?)
\end{enumerate}

\Problema

Considere-se a fórmula que dá o |n|-ésimo \catalan{número de Catalan}:
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
No anexo \ref{sec:codigo} dá-se a função |catdef| que implementa a definição (\ref{eq:cat}) em Haskell.
É fácil de verificar que, à medida que |n| cresce, o tempo que |catdef n| demora a executar degrada-se.
 
Pretende-se uma implementação mais eficiente de $C_n$ que, derivada por recursividade mútua,
não calcule factoriais nenhuns:
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}

No anexo \ref{sec:codigo} é dado um oráculo que pode ajudar a testar |cat|.
Deverá ainda ser comparada a eficiência da solução calculada |cat| com a de |catdef|.

\begin{alert}
\textbf{Sugestão}: Começar por estudar a regra prática que se dá no anexo
\ref{sec:mr} para problemas deste género.
\end{alert}

\Problema

Esta questão aborda um problema que é conhecido pela designação \emph{Largest
Rectangle in Histogram}. Precebe-se facilmente do que se trata olhando para a parte
esquerda da figura abaixo, que mostra o histograma correspondente à sequência numérica:
\begin{code}
h :: [Int]
h = [2,1,5,6,2,3]
\end{code}

\histograma

À direita da mesma figura identifica-se o rectângulo de maior área que é possível inscrever no referido histograma,
com área |10 = 2 * 5|.

Pretende-se a definição de uma função em Haskell
\begin{code}
lrh :: [Int] -> Int
\end{code}
tal que |lrh x| seja a maior área de rectângulos que seja possível inscrever em |x|.

Pretende-se uma solução para o problema que seja simples e estruturada num hilomorfismo baseado num tipo indutivo estudado na disciplina ou definido \emph{on purpose}.

\newpage
\part*{Anexos}

\appendix

\section{Natureza do trabalho a realizar}
\label{sec:documentacao}
Este trabalho teórico-prático deve ser realizado por grupos de 3 alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo em \textbf{todos}
os exercícios do trabalho, para assim poderem responder a qualquer questão
colocada na \emph{defesa oral} do relatório.

Para cumprir de forma integrada os objectivos do trabalho vamos recorrer
a uma técnica de programa\-ção dita ``\litp{literária}'' \cite{Kn92}, cujo
princípio base é o seguinte:
%
\begin{quote}\em
	Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o \textbf{código fonte} e a \textbf{documentação} de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2324t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2324t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no \MaterialPedagogico\
desta disciplina des\-com\-pactando o ficheiro \texttt{cp2324t.zip}.

Como se mostra no esquema abaixo, de um único ficheiro (|lhs|)
gera-se um PDF ou faz-se a interpretação do código \Haskell\ que ele inclui:

	\esquema

Vê-se assim que, para além do \GHCi, serão necessários os executáveis \PdfLatex\ e
\LhsToTeX. Para facilitar a instalação e evitar problemas de versões e
conflitos com sistemas operativos, é recomendado o uso do \Docker\ tal como
a seguir se descreve.

\section{Docker} \label{sec:docker}

Recomenda-se o uso do \container\ cuja imagem é gerada pelo \Docker\ a partir do ficheiro
\texttt{Dockerfile} que se encontra na diretoria que resulta de descompactar
\texttt{cp2324t.zip}. Este \container\ deverá ser usado na execução
do \GHCi\ e dos comandos relativos ao \Latex. (Ver também a \texttt{Makefile}
que é disponibilizada.)

Após \href{https://docs.docker.com/engine/install/}{instalar o Docker} e
descarregar o referido zip com o código fonte do trabalho,
basta executar os seguintes comandos:
\begin{Verbatim}[fontsize=\small]
    $ docker build -t cp2324t .
    $ docker run -v ${PWD}:/cp2324t -it cp2324t
\end{Verbatim}
\textbf{NB}: O objetivo é que o container\ seja usado \emph{apenas} 
para executar o \GHCi\ e os comandos relativos ao \Latex.
Deste modo, é criado um \textit{volume} (cf.\ a opção \texttt{-v \$\{PWD\}:/cp2324t}) 
que permite que a diretoria em que se encontra na sua máquina local 
e a diretoria \texttt{/cp2324t} no \container\ sejam partilhadas.

O grupo deverá visualizar/editar os ficheiros numa máquina local e compilá-los no \container, executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2324t.lhs > cp2324t.tex
    $ pdflatex cp2324t
\end{Verbatim}
\LhsToTeX\ é o pre-processador que faz ``pretty printing'' de código Haskell
em \Latex\ e que faz parte já do \container. Alternativamente, basta executar
\begin{Verbatim}[fontsize=\small]
    $ make
\end{Verbatim}
para obter o mesmo efeito que acima.

Por outro lado, o mesmo ficheiro \texttt{cp2324t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2324t.lhs
\end{Verbatim}

\noindent O grupo deve abrir o ficheiro \texttt{cp2324t.lhs} num editor da sua preferência
e verificar que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Em que consiste o TP}

Em que consiste, então, o \emph{relatório} a que se referiu acima?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2324t.aux
    $ makeindex cp2324t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. (Como já se disse, pode fazê-lo
correndo simplesmente \texttt{make} no \container.)

No anexo \ref{sec:codigo} disponibiliza-se algum código \Haskell\ relativo
aos problemas que são colocados. Esse anexo deverá ser consultado e analisado
à medida que isso for necessário.

Deve ser feito uso da \litp{programação literária} para documentar bem o código que se
desenvolver, em particular fazendo diagramas explicativos do que foi feito e
tal como se explica no anexo \ref{sec:diagramas}.

\begin{alert}
\textbf{Importante:} o grupo deve evitar trabalhar fora deste ficheiro \lhstotex{lhs}
que lhe é fornecido. Se, para efeitos de divisão de trabalho, o decidir fazer,
deve \textbf{regularmente integrar} e validar as soluções que forem sendo
obtidas neste \lhstotex{lhs}, garantindo atempadamente a compatibilidade com este.

Se não o fizer corre o risco de vir a submeter um ficheiro que não corre
no GHCi e/ou apresenta erros na geração do PDF.
\end{alert}

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2TeX} \label{sec:diagramas}

Como primeiro exemplo, estudar o texto fonte (\lhstotex{lhs}) do que está a ler\footnote{
Procure e.g.\ por \texttt{"sec:diagramas"}.} onde se obtém o efeito seguinte:\footnote{Exemplos
tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
     |id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )|
%
\just\equiv{ identity }
%
        |lcbr(
          p1 = f
     )(
          p2 = g
     )|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Regra prática para a recursividade mútua em |Nat0|}\label{sec:mr}

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) pode derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como
exemplo o cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci,
recordar o sistema:
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos de apoio às aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}
Tipos básicos:
\begin{code}
type Votes = Integer
type Deputies = Integer
\end{code}
Dados:
\begin{code}
db :: [(Party, (Votes, Deputies))]
db = map f vote where f(a,b) = (a,(b,0))

vote = [(A,12000),(B,7500),(C,4500),(D,3000)]
\end{code}
Apuramento:
\begin{code}
final = map (id >< p2) . last
total = sum (map snd vote)
wasted = waste history
\end{code}

\subsection*{Problema 3}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}


%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os grupos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o ``layout'' que se fornece.
Não podem ser alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, diagramas e/ou outras funções auxiliares que sejam necessárias.

\begin{alert}
\textbf{Importante}: Não pode ser alterado o texto deste ficheiro fora deste anexo.
\end{alert}

\subsection*{Problema 1}
Ao analisar o problema, percebemos que a resolucao do mesmo dependia do tipo de informação contida no history. Para isso começámos por definir o \textbf{step} e posteriormente o \textbf{waste}.

\begin{code}
step [] = []
step l = aux maxPair l
        where
          maxPair = maximumBy (comparing (p1 . p2)) l
          aux _ [] = []
          aux (maxP, (maxV, maxD)) ((p, (v, d)) : rest)
            | maxP == p && maxD == 0 = (p, (v `div` 2, succ d)) : rest
            | maxP == p = (p, ((v * succ d) `div` (d + 2), succ d)) : rest
            | otherwise = (p, (v, d)) : aux maxPair rest
\end{code}

A cada iteração calculamos o partido com o maior número de votos e guardamos a informação em \textbf{maxPair}.
Se tiver 0 deputados, para obter os "novos" votos, dividimos os votos totais desse partido por 2 e de seguida adicionamos um deputado. 
Se tiver mais que 0 deputados, os votos irão ser a divisão dos votos totais desse partido pelo seu número de deputados mais 2, de seguida aumentamos o número de deputados.
Por fim, se não for o partido com mais votos, mantemos os votos e os deputados inalterados.

\vspace{1em}\vspace{1em}

O \textbf{history} é a aplicação da função \textbf{for} \textbf{step} \textbf{db} em \textbf{i} vezes, que origina uma lista de listas possuindo a informação referente a cada patido (votos, deputados).


\begin{align*}
    0 & \quad [(A,(12000,0)),(B,(7500,0)),(C,(4500,0)),(D,(3000,0))] \\
    1 & \quad [(A,(6000,1)),(B,(7500,0)),(C,(4500,0)),(D,(3000,0))] \\
    2 & \quad [(A,(6000,1)),(B,(3750,1)),(C,(4500,0)),(D,(3000,0))] \\
    3 & \quad [(A,(4000,2)),(B,(3750,1)),(C,(4500,0)),(D,(3000,0))] \\
    4 & \quad [(A,(4000,2)),(B,(3750,1)),(C,(2250,1)),(D,(3000,0))] \\
    5 & \quad [(A,(3000,3)),(B,(3750,1)),(C,(2250,1)),(D,(3000,0))] \\
    6 & \quad [(A,(3000,3)),(B,(2500,2)),(C,(2250,1)),(D,(3000,0))] \\
    7 & \quad [(A,(3000,3)),(B,(2500,2)),(C,(2250,1)),(D,(1500,1))]
\end{align*}

Já o nosso \textbf{waste} soma todos os votos da última lista do \textbf{history}, que contém os votos desperdiçados. 

\begin{code}
waste = sum . map (p1 . p2) . last
\end{code}

\subsection*{Problema 2}
Para a descoberta dos genes \textbf{f} e \textbf{g} referentes ao hilomorfismo \textbf{mergek}, elaboramos o seguinte diagrama:

\begin{eqnarray*}         
\xymatrix@@C=3cm{
    (A^{*})^{*}
           \ar[r]^-{\mathsf{divide}}
           \ar[d]_-{mergeK}
&
    1 + A |><| (A^{*})^{*}
           \ar[d]^-{id + id |><| mergeK}
\\
    A^{*}
&
    1 + A |><| A^{*}
           \ar[l]^-{\mathsf{conquer = [nil, cons]}}
}
\end{eqnarray*}

Genes de |mergek|:
\begin{code}
f = inList

g [] = i1 ()
g l = if filter (/= []) l == []
    then i1 ()
    else i2 (m, l') where
        m = minimum (map head x)
        l' = aux m x
        aux _ [] = []
        aux m (h:t) = if m == head h
                        then tail h : t
                        else h : aux m t 
        x = filter (/= []) l
\end{code}
Na nossa resolução o "núcleo" do algoritmo é realizado em grande parte pelo anamorfismo, ficando como um catamorfismo que é o \textbf{inList}.


\noindent Extensão de |mSort|:

Utilizamos a função \textbf{chunksOf} para dividir a lista em k partes, assegurando que a divisão só ocorre se o comprimento da lista for superior a k. Desta forma, evitamos que o algoritmo entre em ciclo infinito. Posteriormente, utilizamos a função \textbf{mergek} para juntar as partes ordenadas.
\begin{code}
mSortk k [] = []
mSortk k l
    | length l <= 1 = l
    | otherwise = let chunks = chunksOf (if length l <= k then 1 else k) l
                in mergek (map (mSortk k) chunks)
\end{code}
Com uma abordagem que divide a lista em k partes, é possível reduzir significativamente o número de comparações e operações necessárias para ordenar a lista, tornando o algoritmo mais eficiente. Este método beneficia do paralelismo, uma vez que permite dividir a lista em k partes e ordená-las em simultâneo.

Cada parte pode ser ordenada de forma independente e, posteriormente, combinada para formar a lista ordenada final. Isto não só distribui a carga de trabalho, como também reduz o tempo total de execução. Esta abordagem é escalável, podendo ser ajustada para diferentes tamanhos de listas.

\subsection*{Problema 3}
Para a simplificação do algoritmo de Catalan sem recurso ao cálculo dos factoriais
é necessário reescrever a fórmula. A simplificação é a seguinte descrita:

\begin{eqnarray}
C_n = \frac{(2n)!}{(n+1)! (n!) }
\label{eq:cat}
\end{eqnarray}
\begin{eqnarray}
    C_n = \frac{(2n)(2n-1)!}{(n+1)n!*n(n-1)! }
    \label{eq:cat}
\end{eqnarray}
\begin{eqnarray}
    C_n = \frac{2(2n-1)!}{(n+1)n!*(n-1)! }
    \label{eq:cat}
\end{eqnarray}
\begin{eqnarray}
    C_n = \frac{2(2n-1)(2n-2)!}{(n+1)n!*(n-1)(n-2)! }
    \label{eq:cat}
\end{eqnarray}
\hspace{2cm} ...

A continuação da simplificação matemática mostraria que era possível
obter o número de Catalan atual, usando o número de Catalan anterior.

Pelo link da Wikipédia disponibilizada pela equipa docente sabemos que:
\begin{eqnarray}
    C_0 = 1
    \label{eq:cat}
\end{eqnarray}
\begin{eqnarray}
    C_n = \frac{2(2n-1)}{n+1 }*C_{n-1}
    \label{eq:cat}
\end{eqnarray}
Que iremos simplificar para 
\begin{eqnarray}
    C_n = \frac{4n-2}{n+1 }*C_{n-1}
    \label{eq:cat}
\end{eqnarray}
Para reduzir o número de operações.

Sabendo como se escreve 
\begin{eqnarray}C_n\label{eq:cat}\end{eqnarray} 
através de 
\begin{eqnarray}C_{n-1}\label{eq:cat}\end{eqnarray} 
é possível escrever a recursividade mútua do algoritmo.

O nosso \textbf{inic} será composto por um par (a,b) que será inicializado com (1,1).
O loop é responsável por aplicar a função succ ao primeiro elemento e a executar a chamada recursiva no segundo elemento do \textbf{inic}.
A primeira componente serve para guardar a iteração atual, já a segunda guarda o número de Catalan.
Sendo assim, ficamos com o seguinte algoritmo:

\begin{code}
cat = prj . for loop inic
\end{code}
onde:
\begin{code}
loop (a, b) = (a + 1, b * ((4 * a) - 2) `div` (a + 1)) 
inic = (1,1) 
prj = p2
\end{code}

\subsection*{Problema 4}

Diagrama para a resolução do problema:

\begin{eqnarray*}         
\xymatrix@@C=5cm{
    A^{*}
           \ar[r]^-{\mathsf{g}}
           \ar[d]_-{[(subL)]}
&
    1 + A^{*} |><| A^{*}
           \ar[d]^-{id + id |><| subL}
\\
    (A^{*})^{*}
        \ar@@/^/[r]^-{\mathsf{out}}
        \ar[d]_-{(|[maximum . map lR]|)}
&
    1 + A^{*} |><| (A^{*})^{*}
           \ar@@/^/[l]^-{\mathsf{in = [nil, concat]}}
           \ar[d]^-{id + id |><| (|maximum . map lR|)}
\\
    A
&
    1 + A^{*} |><| A
           \ar[l]^-{\mathsf{f}}
}
\end{eqnarray*}

\begin{code}
lrh = (maximum . map lR) . subL


subL [] = []
subL xs = xs : subL (tail xs)


lR [] = 0
lR [x] = x
lR (x:y:xs)
    | x > y     = x
    | x <= y    = x + lR (x:xs)

\end{code}

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2324t}

%----------------- Fim do documento -------------------------------------------%
\end{document}


/* PiffPaff
 * Author: marti
 * Creation date: 05/12/2021
 */
MACHINE PiffPaff
    
SETS BARALHO = {1..108}; DECK1 <: BARALHO ; DECK2 <: BARALHO; MONTE <: BARALHO; LIXEIRA <: BARALHO;  

CONSTANTS PAUS <: BARALHO; COPAS <: BARALHO; OUROS <: BARALHO; ESPADAS <: BARALHO;

VARIABLES jogadorDaVez ,trincasJogador1, trincasJogador2;
    
INVARIANT ((card(DECK1) == 0 & trincasJogador1 == 3)
    || (card(DECK1) == 3 & trincasJogador1 == 2)
    || (card(DECK1) == 6 & trincasJogador1 == 1)
    || (card(DECK1) == 9 & trincasJogador1 == 0))
    || ((card(DECK2) == 0 & trincasJogador2 == 3)
    || (card(DECK2) == 3 & trincasJogador2 == 2)
    || (card(DECK2) == 6 & trincasJogador2 == 1)
    || (card(DECK2) == 9 & trincasJogador2 == 0))
    & not((card(DECK1) == 0 & card(DECK2) == 0))
    & DECK1 /\ DECK2 = {}
    & DECK1 /\ MONTE = {}
    & DECK1 /\ LIXEIRA = {}
    & DECK2 /\ MONTE = {}
    & DECK2 /\ LIXEIRA = {}
    
INITIALISATION 
    trincasJogador1 := 0 ||
    trincasJogador2 := 0 ||
    DECK1 := {22, 3, 9, 10, 55, 92, 7, 108, 4} ||
    DECK2 := {57, 60, 100, 2, 93, 30, 40, 89, 5} ||
    MONTE := BARALHO / (DECK1 \/ DECK2) ||
    LIXEIRA := {} ||
    jogadorDaVez := 0
    
OPERATIONS

comprarDoMonte =
    PRE mm : MONTE
    THEN 
        IF (jogadorDaVez == 1) THEN
           DECK1 := DECK1 \/ {mm};
           jogadorDaVez := 2;
        ELSE
           DECK2 := DECK2 \/ {mm};
           jogadorDaVez := 1;
        END;
        descartar();
    END;
   
comprarDoMonte(jj) =
    PRE ll : LIXEIRA
    THEN 
        IF (jogadorDaVez == 1) THEN
           DECK1 := DECK1 \/ {ll};
           jogadorDaVez := 2;
        ELSE
           DECK2 := DECK2 \/ {ll};
           jogadorDaVez := 1;
        END;
        descartar();
    END;
   
abaixarTrinca =

descartar(jj) = 
    PRE ((card(DECK1) == 10 || card(DECK2) == 10) 
        || (card(DECK1) == 7 || card(DECK2) == 7)
        || (card(DECK1) == 4 || card(DECK2) == 4))
    IF (jogadorDaVez == 1) THEN
        CHOICE dd : DECK1
            LIXEIRA := LIXEIRA \/ {dd};
            DECK1 := DECK1 / {dd};
    ELSE 
        CHOICE dd : DECK2
            LIXEIRA := LIXEIRA \/ {dd};
            DECK1 := DECK1 / {dd};
    END;
    
passarAVez = 
    IF (jogadorDaVez == 1) THEN
        jogadorDaVez := 2;
    ELSE
        jogadorDaVez := 1;
    END;

END
MACHINE PiffPaff

SETS BARALHO; DECK1; TRINCAS; DECK2; MONTE; LIXEIRA

CONSTANTS PAUS, COPAS, OUROS, ESPADAS

VARIABLES jogadorDaVez ,trincasJogador1, trincasJogador2

INVARIANT BARALHO = 1..108
    & DECK1 <: BARALHO
    & DECK2 <: BARALHO
    & TRINCAS <: POW(BARALHO)
    & MONTE <: BARALHO
    & LIXEIRA <: BARALHO
    & PAUS <: BARALHO
    & COPAS <: BARALHO
    & OUROS <: BARALHO
    & ESPADAS <: BARALHO
    & ((card(DECK1) = 0 & trincasJogador1 = 3)
    or (card(DECK1) = 3 & trincasJogador1 = 2)
    or (card(DECK1) = 6 & trincasJogador1 = 1)
    or (card(DECK1) = 9 & trincasJogador1 = 0))
    & ((card(DECK2) = 0 & trincasJogador2 = 3)
    or (card(DECK2) = 3 & trincasJogador2 = 2)
    or (card(DECK2) = 6 & trincasJogador2 = 1)
    or (card(DECK2) = 9 & trincasJogador2 = 0))
    & not((card(DECK1) = 0 & card(DECK2) = 0))
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

descartar = 
    PRE (jogadorDaVez = 1 & (card(DECK1) = 10 or card(DECK1) = 7 or card(DECK1) = 4)) or (jogadorDaVez = 2 & (card(DECK2) = 10 or card(DECK2) = 7 or card(DECK2) = 4)) 
    THEN
        IF (jogadorDaVez = 1) THEN
            ANY dd WHERE dd : DECK1 THEN
                LIXEIRA := LIXEIRA \/ {dd} || DECK1 := DECK1 / {dd};
            END
        ELSE 
            ANY dd WHERE dd : DECK2 THEN
                LIXEIRA := LIXEIRA \/ {dd} || DECK1 := DECK1 / {dd};
            END
        END
    END;

comprarDoMonte =
    ANY mm WHERE mm : MONTE    
    THEN 
        IF (jogadorDaVez = 1) THEN
           DECK1 := DECK1 \/ {mm} || jogadorDaVez := 2
        ELSE
           DECK2 := DECK2 \/ {mm} || jogadorDaVez := 1
        END
        //descartar()
    END;
   
comprarDaLixeira =
    ANY ll WHERE ll : LIXEIRA
    THEN 
        IF (jogadorDaVez = 1) THEN
           DECK1 := DECK1 \/ {ll} || jogadorDaVez := 2
        ELSE
           DECK2 := DECK2 \/ {ll} || jogadorDaVez := 1
        END
        //descartar()
    END;
   
abaixarTrinca = 
    IF (jogadorDaVez = 1) THEN
        SELECT c1: DECK1, c2 : DECK1; c3 : DECK1 THEN
            IF (verificaTrinca({c1, c2, c3}) == TRUE) THEN
                DECK1 := DECK1 / {c1, c2, c3} || trincasJogador1 := trincasJogador1 + 1
            END
            jogadorDaVez := 2
         END
     ELSE
         SELECT c1: DECK2, c2 : DECK2; c3 : DECK2 THEN
             IF (verificaTrinca({c1,c2,c3}) == TRUE) THEN
                DECK2 := DECK2 / {c1, c2, c3} ||  trincasJogador2 := trincasJogador2 + 1
             END
             jogadorDaVez := 1
          END
     END;
     
vv <-- verificarTrinca(tt) = 
    PRE tt : POW BARALHO
    THEN
        IF (tt : TRINCAS) THEN
            vv := TRUE;
        ELSE
            vv:= FALSE;
        END
    END;
        
    
passarAVez = 
    IF (jogadorDaVez == 1) THEN
        jogadorDaVez := 2
    ELSE
        jogadorDaVez := 1
    END
END

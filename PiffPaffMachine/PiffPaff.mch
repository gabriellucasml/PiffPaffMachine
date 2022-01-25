MACHINE PiffPaff
       
SETS BARALHO; TRINCAS; PAUS; COPAS; OUROS; ESPADAS 
     
VARIABLES deck1, deck2, monte, lixeira, jogadorDaVez ,trincasJogador1, trincasJogador2, lock, vencedor

INVARIANT deck1 <: BARALHO & deck2 <: BARALHO & monte <: BARALHO & lixeira <: BARALHO
    & monte /\ lixeira = {}
    & lixeira:FIN(lixeira)
    & card(lixeira) < card(BARALHO) - 2*9 // baralho menos os 2 decks
    & card(monte) < card(BARALHO) - 2*9 // baralho menos os 2 decks
    & trincasJogador1 : NATURAL & trincasJogador1 >= 0 & trincasJogador1 <= 3
    & trincasJogador2 : NATURAL & trincasJogador2 >= 0 & trincasJogador2 <= 3
    & jogadorDaVez : NATURAL & (jogadorDaVez = 1 or jogadorDaVez = 2)
    & vencedor <: 0..2 //Caso vencedor seja 1 o jogador 1 venceu, caso seja 2 o jogador 2 venceu, e em 0 o jogo ainda está rolando
    & lock : BOOL
    /*& (card(deck1) : {0, 3, 6, 9} & lock = FALSE) 
      or (card(deck1) : {1, 4, 7, 10} & lock = TRUE)
    & (card(deck2) : {0, 3, 6, 9} & lock = FALSE) 
      or (card(deck2) : {1, 4, 7, 10} & lock = TRUE)
    */
    & deck1 /\ deck2 = {}
    & deck1 /\ monte = {}
    & deck1 /\ lixeira = {}
    & deck2 /\ monte = {}

    
INITIALISATION 
    trincasJogador1 := 0 ||
    trincasJogador2 := 0 ||
    deck1 := {22, 3, 9, 10, 55, 92, 7, 108, 4} ||
    deck2 := {57, 60, 100, 2, 93, 30, 40, 89, 5} ||
    monte := BARALHO / (deck1 \/ deck2) ||
    lixeira := {} ||
    jogadorDaVez := 0 ||
    lock := FALSE ||
    vencedor := 0
    
OPERATIONS

comprarDoMonte =
    PRE card(monte) > 0 & lock = FALSE 
    THEN
        IF (jogadorDaVez = 1) THEN
            ANY dd WHERE dd : deck1 THEN
                monte := monte / {dd} ||
                deck1 := deck1 \/ {dd} ||
                lock := TRUE
            END
        ELSE 
            ANY dd WHERE dd : deck2 THEN
                monte := monte / {dd} ||
                deck2 := deck1 \/ {dd} ||
                lock := TRUE
            END
        END
    END;
   
comprarDaLixeira =
    PRE card(lixeira) > 0 & lock = FALSE
    THEN
        IF (jogadorDaVez = 1) THEN
            ANY dd WHERE dd : deck1 THEN
                lixeira := lixeira / {dd} ||
                deck1 := deck1 \/ {dd} ||
                lock := TRUE
            END
        ELSE 
            ANY dd WHERE dd : deck2 THEN
                lixeira := lixeira / {dd} ||
                deck2 := deck2 \/ {dd} ||
                lock := TRUE
            END
        END
    END;
   

/*abaixarTrinca = 
    PRE (jogadorDaVez = 1 & trincasJogador1 > 0) or (jogadorDaVez = 2 & trincasJogador2 > 0)
    THEN
        IF (jogadorDaVez = 1) THEN
            SELECT c1: deck1 THEN
                SELECT c2 : deck1 THEN
                    SELECT c3 : deck1 THEN
                        IF {c1, c2, c3} : TRINCAS) THEN
                            deck1 := deck1 / {c1, c2, c3} || trincasJogador1 := trincasJogador1 + 1
                        END
                        jogadorDaVez := 2
                    END
                END
            END
        ELSE
            SELECT c1: deck2 THEN
                SELECT c2 : deck2 THEN
                    SELECT c3 : deck2 THEN
                        IF {c1, c2, c3} : TRINCAS) THEN
                            deck2 := deck2 / {c1, c2, c3} || trincasJogador1 := trincasJogador1 + 1
                        END
                        jogadorDaVez := 1
                    END
                END
            END
        END    
    END; 
*/

descartar = 
    PRE lock = TRUE
    THEN
        IF (jogadorDaVez = 1) THEN
            ANY dd WHERE dd : deck1 THEN
                lixeira := lixeira \/ {dd} ||
                deck1 := deck1 / {dd} || 
                lock := FALSE ||
                jogadorDaVez := 2
             END
    
        ELSE 
            ANY dd WHERE dd : deck2 THEN
                lixeira := lixeira \/ {dd} ||
                deck2 := deck2 / {dd} || 
                lock := FALSE ||
                jogadorDaVez := 1
             END
        END
    END;
    
passarAVez = 
    PRE lock = FALSE
    THEN
        IF (jogadorDaVez = 1) THEN
            jogadorDaVez := 2
        ELSE
            jogadorDaVez := 1
        END
    END

END

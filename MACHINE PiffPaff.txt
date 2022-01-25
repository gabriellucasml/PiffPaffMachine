MACHINE           PiffPaff
    
SETS              BARALHO
    
CONSTANTS         TRINCAS

PROPERTIES        BARALHO:FIN(BARALHO)
                  & TRINCAS <: POW(BARALHO)

VARIABLES         deck1, deck2, monte, lixeira, jogadorDaVez, vencedor, lock, pM, pL, num, pD1, pD2

INVARIANT         deck1 <: BARALHO 
                  & deck2 <: BARALHO
                  & monte <: BARALHO
                  & lixeira <: BARALHO
                  & lixeira:FIN(lixeira)
                  & monte:FIN(monte)
                  & jogadorDaVez : NATURAL & (jogadorDaVez = 1 or jogadorDaVez = 2)
                  & card(lixeira) <= 108
                  & card(monte) <= 108
                  & vencedor : {0, 1, 2}
                  & lock : BOOL
                  & card(deck1) : {0,1,3,4,6,7,9,10}
                  & deck1 /\ deck2 = {}
                  & deck1 /\ monte = {}
                  & deck1 /\ lixeira = {}
                  & deck2 /\ monte = {}
                  & num = {1}
                  & pM : num --> monte
                  & pL : num --> monte
                  & pD1 : NAT --> deck1
                  & pD2 : NAT --> deck2
                  
                  
INITIALISATION    deck1 := {} 
                  || deck2 := {}
                  || monte := {}
                  || lixeira := {}
                  || jogadorDaVez := 1
                  || vencedor := 0
                  || lock := FALSE
                  || num := {1}
                  || pM :: num --> monte
                  || pL :: num --> lixeira
                  || pD1 :: NAT --> deck1
                  || pD2 :: NAT --> deck2
                  


OPERATIONS

mm <-- comprarDoMonte =
    PRE card(monte) > 0 & lock = FALSE & mm : monte
    THEN
        IF (jogadorDaVez = 1) THEN      
            mm := pM(1) ||
            monte := monte - {mm} ||
            deck1 := deck1 \/ {mm} ||
            lock := TRUE                     
        ELSE 
            mm := pM(1) ||
            monte := monte - {mm} ||
            deck2 := deck2 \/ {mm} ||
            lock := TRUE 
        END
    END;
    
ll <-- comprarDaLixeira =
    PRE card(lixeira) > 0 & lock = FALSE & ll : lixeira
    THEN
        IF (jogadorDaVez = 1) THEN
            ll := pL(1) || 
            lixeira := lixeira - {ll} ||
            deck1 := deck1 \/ {ll} ||
            lock := TRUE
        ELSE 
            ll := pL(1) ||
            lixeira := lixeira - {ll} ||
            deck2 := deck2 \/ {ll} ||
            lock := TRUE
        END
    END;
   

dd <-- abaixarTrinca(c1, c2, c3) = 
    PRE c1 : NAT & c2 : NAT & c3 : NAT & c1 /= c2 & c2 /= c3 & c1 /= c3 & dd <: BARALHO
    THEN
        IF (jogadorDaVez = 1) THEN
            dd := {pD1(c1)} \/ {pD1(c2)} \/ {pD1(c3)} ||      
            IF (dd : TRINCAS) THEN
                deck1 := deck1 - dd || jogadorDaVez := 2 ||
                IF(card(deck1) = 0) THEN
                    vencedor := 1
                END
            END
        ELSE
            dd :=  {pD2(c1)} \/ {pD2(c2)} \/ {pD2(c3)} ||      
            IF (dd : TRINCAS) THEN
                deck2 := deck2 - dd || jogadorDaVez := 2 ||
                IF(card(deck1) = 0) THEN
                    vencedor := 1
                END
            END
        END    
    END; 


dd <-- descartar(cc) = 
    PRE lock = TRUE & dd : BARALHO & cc : NAT & cc >= 1 & cc <= 9
    THEN
        IF (jogadorDaVez = 1) THEN
            dd := pD1(cc) ||
            lixeira := lixeira \/ {dd} ||
            deck1 := deck1 - {dd} || 
            lock := FALSE ||
            jogadorDaVez := 2
  
        ELSE 
            dd := pD2(cc) ||
            lixeira := lixeira \/ {dd} ||
            deck2 := deck2 - {dd} || 
            lock := FALSE ||
            jogadorDaVez := 1
        END
    END;
    
jj <-- passarAVez = 
    PRE lock = FALSE & jj : NAT
    THEN
        IF (jogadorDaVez = 1) THEN
            jj := 2 || jogadorDaVez := 2
        ELSE
            jj := 1 || jogadorDaVez := 1
        END
    END

END
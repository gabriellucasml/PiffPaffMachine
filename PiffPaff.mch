MACHINE           PiffPaff         

SETS              BARALHO

CONSTANTS         trincas, espadas, paus, ouros, copas, query, cartas

PROPERTIES        espadas = 0..25   //>-> BARALHO
                  & paus  = 26..51  //>-> BARALHO
                  & ouros = 52..77  //>-> BARALHO
                  & copas = 78..103 //>-> BARALHO
                  & query : BARALHO >->-1..103
 	              & cartas : -1..103 >-> BARALHO
                  & trincas = POW(NAT)
                  /*& trincas = {xx,yy,zz | xx : NAT & yy : NAT & zz: NAT & (xx mod 13 = yy mod 13 
                           & xx mod 13 = zz mod 13 
                           & yy mod 13 = zz mod 13 
                           & (not(xx : espadas & yy : espadas))
                           & (not(xx : espadas & zz : espadas))
                           & (not(yy : espadas & zz : espadas))
                           & (not(xx : paus & yy : paus))
                           & (not(xx : paus & zz : paus))
                           & (not(yy : paus & zz : paus))
                           & (not(xx : ouros & yy : ouros))
                           & (not(xx : ouros & zz : ouros))
                           & (not(yy : ouros & zz : ouros))
                           & (not(xx : copas & yy : copas))
                           & (not(xx : copas & zz : copas))
                           & (not(yy : copas & zz : copas))
                          ) or ((((xx mod 13) + 1 = yy mod 13  & (yy mod 13) + 1 = zz mod 13) or // x < y < z
                                ((xx mod 13) + 1 = zz mod 13  & (zz mod 13) + 1 = yy mod 13) or // x < z < y
                                ((yy mod 13) + 1 = xx mod 13  & (xx mod 13) + 1 = zz mod 13) or // y < x < z
                                ((yy mod 13) + 1 = zz mod 13  & (zz mod 13) + 1 = xx mod 13) or // y < z < x
                                ((zz mod 13) + 1 = xx mod 13  & (xx mod 13) + 1 = yy mod 13) or // z < x < y
                                ((zz mod 13) + 1 = yy mod 13  & (yy mod 13) + 1 = xx mod 13)) // z < y < x
                                & ((xx : espadas & yy : espadas & zz : espadas) or
                                   (xx : paus & yy : paus & zz : paus) or
                                   (xx : ouros & yy : ouros & zz : ouros) or
                                   (xx : copas & yy : copas & zz : copas)))}*/

VARIABLES         deck1, deck2, monte, lixeira, mesa, jogadorDaVez, vencedor, lock

INVARIANT         deck1 :   -1..8 --> BARALHO       
                  & deck2 :  -1..8 --> BARALHO
                  & monte : 0..103 --> BARALHO
                  & mesa : 0..103 --> BARALHO
                  & lixeira : -1..103 --> BARALHO
                  & jogadorDaVez : NATURAL & (jogadorDaVez = 1 or jogadorDaVez = 2)
                  & card(lixeira) = 105
                  & card(monte) = 104
                  & vencedor : {0, 1, 2}
                  & lock : BOOL                
INITIALISATION    deck1 := {-1|->cartas(-1), 0|->cartas(2),1|->cartas(22),2|->cartas(13),3|->cartas(84),4|->cartas(74),5|->cartas(24),6|->cartas(100),7|->cartas(64),8|->cartas(82)}
                  || deck2 := {-1|->cartas(-1), 0|->cartas(3),1|->cartas(96),2|->cartas(45),3|->cartas(12),4|->cartas(48),5|->cartas(102),6|->cartas(98),7|->cartas(59),8|->cartas(60)}
                  || monte := { 0|->cartas(0), 1|->cartas(1), 2|->cartas(-1), 3|->cartas(-1), 4|->cartas(4), 5|->cartas(5), 6|->cartas(6), 7|->cartas(7), 8|->cartas(8), 9|->cartas(9), 10|->cartas(10), 11|->cartas(11), 12|->cartas(-1), 13|->cartas(-1), 14|->cartas(14), 15|->cartas(15), 16|->cartas(16), 17|->cartas(17), 18|->cartas(18), 19|->cartas(19), 20|->cartas(20), 21|->cartas(21), 22|->cartas(-1), 23|->cartas(23), 24|->cartas(-1), 25|->cartas(25), 26|->cartas(26), 27|->cartas(27), 28|->cartas(28), 29|->cartas(29), 30|->cartas(30), 31|->cartas(31), 32|->cartas(32), 33|->cartas(33), 34|->cartas(34), 35|->cartas(35), 36|->cartas(36), 37|->cartas(37), 38|->cartas(38), 39|->cartas(39), 40|->cartas(40), 41|->cartas(41), 42|->cartas(42), 43|->cartas(43), 44|->cartas(44), 45|->cartas(-1), 46|->cartas(46), 47|->cartas(47), 48|->cartas(-1), 49|->cartas(49), 50|->cartas(50), 51|->cartas(51), 52|->cartas(52), 53|->cartas(53), 54|->cartas(54), 55|->cartas(55), 56|->cartas(56), 57|->cartas(57), 58|->cartas(58), 59|->cartas(-1), 60|->cartas(-1), 61|->cartas(61), 62|->cartas(62), 63|->cartas(63), 64|->cartas(-1), 65|->cartas(65), 66|->cartas(66), 67|->cartas(67), 68|->cartas(68), 69|->cartas(69), 70|->cartas(70), 71|->cartas(71), 72|->cartas(72), 73|->cartas(73), 74|->cartas(-1), 75|->cartas(75), 76|->cartas(76), 77|->cartas(77), 78|->cartas(78), 79|->cartas(79), 80|->cartas(80), 81|->cartas(81), 82|->cartas(-1), 83|->cartas(83), 84|->cartas(-1), 85|->cartas(85), 86|->cartas(86), 87|->cartas(87), 88|->cartas(88), 89|->cartas(89), 90|->cartas(90), 91|->cartas(91), 92|->cartas(92), 93|->cartas(93), 94|->cartas(94), 95|->cartas(95), 96|->cartas(-1), 97|->cartas(97), 98|->cartas(-1), 99|->cartas(99), 100|->cartas(-1), 101|->cartas(101), 102|->cartas(-1), 103 |-> cartas(103)}
                  
	|| lixeira :=  { -1|->cartas(-1),0|->cartas(-1),1|->cartas(-1),2|->cartas(-1),3|->cartas(-1),4|->cartas(-1),5|->cartas(-1),6|->cartas(-1),7|->cartas(-1),8|->cartas(-1),9|->cartas(-1),10|->cartas(-1),11|->cartas(-1),12|->cartas(-1),13|->cartas(-1),14|->cartas(-1),15|->cartas(-1),16|->cartas(-1),17|->cartas(-1),18|->cartas(-1),19|->cartas(-1),20|->cartas(-1),21|->cartas(-1),22|->cartas(-1),23|->cartas(-1),24|->cartas(-1),25|->cartas(-1),26|->cartas(-1),27|->cartas(-1),28|->cartas(-1),29|->cartas(-1),30|->cartas(-1),31|->cartas(-1),32|->cartas(-1),33|->cartas(-1),34|->cartas(-1),35|->cartas(-1),36|->cartas(-1),37|->cartas(-1),38|->cartas(-1),39|->cartas(-1),40|->cartas(-1),41|->cartas(-1),42|->cartas(-1),43|->cartas(-1),44|->cartas(-1),45|->cartas(-1),46|->cartas(-1),47|->cartas(-1),48|->cartas(-1),49|->cartas(-1),50|->cartas(-1),51|->cartas(-1),52|->cartas(-1),53|->cartas(-1),54|->cartas(-1),55|->cartas(-1),56|->cartas(-1),57|->cartas(-1),58|->cartas(-1),59|->cartas(-1),60|->cartas(-1),61|->cartas(-1),62|->cartas(-1),63|->cartas(-1),64|->cartas(-1),65|->cartas(-1),66|->cartas(-1),67|->cartas(-1),68|->cartas(-1),69|->cartas(-1),70|->cartas(-1),71|->cartas(-1),72|->cartas(-1),73|->cartas(-1),74|->cartas(-1),75|->cartas(-1),76|->cartas(-1),77|->cartas(-1),78|->cartas(-1),79|->cartas(-1),80|->cartas(-1),81|->cartas(-1),82|->cartas(-1),83|->cartas(-1),84|->cartas(-1),85|->cartas(-1),86|->cartas(-1),87|->cartas(-1),88|->cartas(-1),89|->cartas(-1),90|->cartas(-1),91|->cartas(-1),92|->cartas(-1),93|->cartas(-1),94|->cartas(-1),95|->cartas(-1),96|->cartas(-1),97|->cartas(-1),98|->cartas(-1),99|->cartas(-1),100|->cartas(-1),101|->cartas(-1),102|->cartas(-1),103|->cartas(-1)}
                  
	|| mesa :=  { 0|->cartas(-1),1|->cartas(-1),2|->cartas(-1),3|->cartas(-1),4|->cartas(-1),5|->cartas(-1),6|->cartas(-1),7|->cartas(-1),8|->cartas(-1),9|->cartas(-1),10|->cartas(-1),11|->cartas(-1),12|->cartas(-1),13|->cartas(-1),14|->cartas(-1),15|->cartas(-1),16|->cartas(-1),17|->cartas(-1),18|->cartas(-1),19|->cartas(-1),20|->cartas(-1),21|->cartas(-1),22|->cartas(-1),23|->cartas(-1),24|->cartas(-1),25|->cartas(-1),26|->cartas(-1),27|->cartas(-1),28|->cartas(-1),29|->cartas(-1),30|->cartas(-1),31|->cartas(-1),32|->cartas(-1),33|->cartas(-1),34|->cartas(-1),35|->cartas(-1),36|->cartas(-1),37|->cartas(-1),38|->cartas(-1),39|->cartas(-1),40|->cartas(-1),41|->cartas(-1),42|->cartas(-1),43|->cartas(-1),44|->cartas(-1),45|->cartas(-1),46|->cartas(-1),47|->cartas(-1),48|->cartas(-1),49|->cartas(-1),50|->cartas(-1),51|->cartas(-1),52|->cartas(-1),53|->cartas(-1),54|->cartas(-1),55|->cartas(-1),56|->cartas(-1),57|->cartas(-1),58|->cartas(-1),59|->cartas(-1),60|->cartas(-1),61|->cartas(-1),62|->cartas(-1),63|->cartas(-1),64|->cartas(-1),65|->cartas(-1),66|->cartas(-1),67|->cartas(-1),68|->cartas(-1),69|->cartas(-1),70|->cartas(-1),71|->cartas(-1),72|->cartas(-1),73|->cartas(-1),74|->cartas(-1),75|->cartas(-1),76|->cartas(-1),77|->cartas(-1),78|->cartas(-1),79|->cartas(-1),80|->cartas(-1),81|->cartas(-1),82|->cartas(-1),83|->cartas(-1),84|->cartas(-1),85|->cartas(-1),86|->cartas(-1),87|->cartas(-1),88|->cartas(-1),89|->cartas(-1),90|->cartas(-1),91|->cartas(-1),92|->cartas(-1),93|->cartas(-1),94|->cartas(-1),95|->cartas(-1),96|->cartas(-1),97|->cartas(-1),98|->cartas(-1),99|->cartas(-1),100|->cartas(-1),101|->cartas(-1),102|->cartas(-1),103|->cartas(-1)}
                
	|| jogadorDaVez := 1
                  || vencedor := 0
                  || lock := FALSE
 
 
OPERATIONS

comprarDoMonte(cc) =
    PRE card(monte|>>{cartas(-1)}) > 0 & lock = FALSE & cc = 0
    THEN
        IF (jogadorDaVez = 1) THEN
            deck1(-1) := monte(cc)                      
        ELSE 
            deck2(-1) := monte(cc) 
        END ||
        monte(cc) := cartas(-1) ||
        lock := TRUE 
    END;
    
comprarDaLixeira(cc) =
    PRE card(lixeira|>>{cartas(-1)}) > 0 & lock = FALSE & cc = 0
    THEN
        IF (jogadorDaVez = 1) THEN
            deck1(-1) := lixeira(cc)
        ELSE 
            deck2(-1) := lixeira(cc) 
        END ||
        lixeira := lixeira <+ {0 |-> lixeira(card(lixeira|>>{cartas(-1)})), card(lixeira|>>{cartas(-1)})|-> cartas(-1)} ||
        lock := TRUE
    END;
   

abaixarTrinca(c1, c2, c3) = 
    PRE c1 : NAT & c2 : NAT & c3 : NAT & 
        c1 /= c2 & c2 /= c3 & c1 /= c3 &
        c1 < 8 & c2 < 8 & c3 < 8 &
        c1 >= 0 & c2 >= 0 & c3 >= 0
    THEN
        IF (jogadorDaVez = 1) THEN
            IF ({query(deck1(c1)),query(deck1(c2)),query(deck1(c3))} : trincas) THEN
                mesa := mesa <+ {card(mesa |>> {cartas(-1)}) |-> deck1(c1), 
                            (card(mesa |>> {cartas(-1)}) + 1) |-> deck1(c2),
                            (card(mesa |>> {cartas(-1)}) + 2) |-> deck1(c3)} || 
                deck1 := deck1 <+ {c1 |-> deck1(-1), c2 |-> deck1(-1), c3 |-> deck1(-1)} ||
                jogadorDaVez := 2 ||
                IF(card(deck1 |>>{deck1(-1)}) = 0) THEN
                    vencedor := 1
                END
            END
        ELSE      
            IF ({query(deck2(c1)),query(deck2(c2)),query(deck2(c3))} : trincas) THEN
                mesa := mesa <+ {card(mesa |>> {cartas(-1)}) |-> deck2(c1), 
                            (card(mesa |>> {cartas(-1)}) + 1) |-> deck2(c2),
                            (card(mesa |>> {cartas(-1)}) + 2) |-> deck2(c3)} || 
                deck2 := deck2 <+ {c1 |-> deck2(-1), c2 |-> deck2(-1), c3 |-> deck2(-1)} ||
                jogadorDaVez := 2 ||
                IF(card(deck2 |>>{deck2(-1)}) = 0) THEN
                    vencedor := 2
                END
            END
        END    
    END; 


descartar(cc) = 
    PRE lock = TRUE  & cc : NAT & cc >= 0 & cc < 9
    THEN
        IF (jogadorDaVez = 1) THEN
            IF(card(lixeira |>>{cartas(-1)}) > 0) THEN
                lixeira := lixeira <+ {card(lixeira |>>{cartas(-1)}) |-> lixeira(0), 0 |-> deck1(cc)}
            ELSE
                lixeira(card(lixeira |>>{cartas(-1)})) := deck1(cc)
            END ||
            deck1(cc) := cartas(-1) || 
            lock := FALSE ||
            jogadorDaVez := 2
        ELSE 
            IF(card(lixeira |>>{cartas(-1)}) > 0) THEN
                lixeira := lixeira <+ {card(lixeira |>>{cartas(-1)}) |-> lixeira(0), 0 |-> deck2(cc)}
            ELSE
                lixeira(card(lixeira |>>{cartas(-1)})) := deck2(cc)
            END ||
            deck2(cc) := cartas(-1) || 
            lock := FALSE ||
            jogadorDaVez := 1
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
    END;

jj<-- jogadorQuery =
    jj := jogadorDaVez;

ll <-- topoLixeira =
    ll := lixeira(0)
END
# JML

**JML** (Java Modeling Language) è un linguaggio di specifica formale.

## Sintassi

Lo schema generale di una specifica in JML è il seguente:
```java
// OVERVIEW: descrizione della specifica
//@ assignable <parametri che possono essere 
//@    modificati dal metodo>;
//@ requires <precondizione>
//@ ...;
//@ ensures <postcondizione>
//@ ...;
//@ signals (<tipo eccezione 1> e)
//@ <postcondizione nel caso di eccezione 1>
//@ ...;
//@ signals (<tipo eccezione 2> e)
//@ <postcondizione nel caso di eccezione 2>
//@ ...;
```
Ogni riga della specifica (dopo l'`OVERVIEW`) inizia con `//@ `.
Alla fine di ciascun "blocco" (`assignable`, `requires`, ...) è necessario aggiungere `;`.
Omettere il blocco `requires` equivale a scrivere `//@ requires true;`.
Omettere il blocco `ensures` equivale a scrivere `//@ ensures true;`.
Nella condizione del blocco `signals` possiamo fare riferimento all'oggetto eccezione `e` (il nome è arbitrario).

### Condizioni

Le condizioni in JML (precondizioni e postcondizioni) sono espressioni booleane di Java (con alcuni operatori e quantificatori aggiuntivi) che non alterano lo stato degli oggetti che descrivono: non si possono usare assegnamenti (`=`), incrementare le variabili intere (`++`), etc. Gli unici metodi che si possono invocare sono quelli che non modificano lo stato degli oggetti a cui appartengono o dei parametri che gli vengono passati (si dicono **metodi puri**).

#### Operatori booleani aggiuntivi

Siano `a` e `b` due condizioni JML, allora le seguenti sono valide condizioni JML:

- `a ==> b`: `a` implica `b`
- `a <== b`: `b` implica `a`
- `a <==> b`: `a` se e solo se `b`
- `a <=!=> b`: `!(a <==> b)`

#### `\old`

L'operatore `\old(<espressione>)` prende in input una espressione che può essere una condizione JML oppure una espressione Java che non ha "effetti collaterali" (non si può utilizzare `++`, `=`, metodi **non** puri, etc.) e restituisce il risultato che si ottiene valutando tale espressione nel momento della chiamata del metodo che stiamo specificando.
Notare che, valutando una espressione Java (tra quelle ammissibili), `\old` in generale non restituisce valori booleani.
Non ha senso utilizzare `\old` nel blocco `requires` dato che lì stiamo specificando ciò che deve essere vero **prima** che il metodo venga eseguito.

#### Quantificatori

Sia `T` un generico tipo di Java ed `a(t)`, `b(t)` due condizioni JML definite su un oggetto `t` di tipo `T` (ad esempio se `T = int`, `a(t) = t > 1729`), allora le seguenti sono valide condizioni JML:

- `(\forall T t; a(t); b(t))`: per ogni oggetto del tipo `T` se `a(t)` allora `b(t)`
- `(\exists T t; a(t); b(t))`: esiste un oggetto del tipo `T` tale che `a(t)` e `b(t)`
- `(\num_of T t; a(t); b(t))`: restituisce il numero di oggetti `t` tale che `a(t)` e `b(t)`

Nel caso `T` non sia un tipo primitivo assumiamo `t != null`.

#### Operatori di aggragazione

Sia `T` un generico tipo di Java ed `N` uno dei tipi numerici primitivi di Java (`int`, `float`, ...).
Sia `a(t)` una condizione JML definita sull'oggetto `t` di tipo `T`.
Sia `b : T -> N` una funzione (in senso matematico) implementata attraverso Java. Ad esempio:
`T = String`, `N = int`, `a(t) = !t.isEmpty() && t.charAt(0) == 'e'`, `b(t) = t.length()`.
Allora possiamo applicare i seguenti operatori di aggragazione:

- `(\sum T t; a(t); b(t))`: restituisce la somma `b(t_1) + b(t_2) + ...` per tutti i `t_i` tali che `a(t_i)`
- `(\product T t; a(t); b(t))`: restituisce il prodotto `b(t_1)*b(t_2)*...` per tutti i `t_i` tali che `a(t_i)`
- `(\max T t; a(t); b(t))`: restituisce il massimo tra `b(t_1), b(t_2), ...` per tutti i `t_i` tali che `a(t_i)`
- `(\min T t; a(t); b(t))`: restituisce il minimo tra `b(t_1), b(t_2), ...` per tutti i `t_i` tali che `a(t_i)`

### `\result`

Se stiamo scrivendo la specifica di un metodo NON `void`, possiamo fare riferimento al valore restituito con la keyword `\result`.
Ha senso utilizzare `\result` solo nell'`ensures` (in `requires` il metodo non è ancora stato eseguito, `signals` specifica la postcondizione qualora venga restituita un'eccezione).

### `assignable`

Il blocco `assignable` nella specifica permette di esplicitare i parametri (di tipo riferimento) che vengono modificati dal metodo.
Omettere `assignable` significa che tutti i parametri possono essere modificati.

Se un metodo non modifica nessuno dei parametri possiamo usare la keyword `\nothing`:
`//@ assignable \nothing;`.

Consideriamo il seguente metodo:
```java
public static void metodo(S s, T t, U u) {
    ...
}
```

---

Per specificare che `s` e `t` vengono modificati, ma non `u`, possiamo aggiungere nella specifica:
`//@ assignable s, t;`

Supponiamo di voler specificare che un array `a[]` venga modificato da un metodo di cui stiamo scrivendo la specifica:

- `//@ assignable a[*];`: ogni elemento di `a` può essere modificato
- `//@ assignable a[5];`: solo l'elemento `a[5]` può essere modificato
- `//@ assignable a[1..8];`: gli elementi `a[1]`, `a[2]`, ..., `a[8]` possono essere modificati

### Commenti

A volte è utile inserire all'interno delle condizioni JML delle specifiche informali.
Per farlo si utilizzano i commenti, esprimibili attraverso la seguente sintassi: `(* <commento> *)`.
Ciascun commento al momento della valutazione della condizione è da intendersi con valore `true`.

## Semantica

### Precondizione

La **precondizione** è la condizione sulla base della quale è definita la specifica: se la precondizione non dovesse essere rispettata allora non è detto che il metodo si comporti secondo la specifica (in generale non lo farà, qualsiasi comportamento è ammesso).
In JML è possibile esprimere una precondizione del metodo che stiamo specificando attraverso il blocco `requires`.
Nel caso in cui la precondizione sia `true` il metodo "non ha una precondizione": la sua specifica è valida a prescindere dei parametri passati.
Un metodo con precondizione `true` si dice **totale**, altrimenti si dice **parziale**.

### Postcondizione

La **postcondizione** esplicita una serie di "effetti" garantiti al termine dell'esecuzione del metodo che stiamo specificando, assumendo che la precondizione fosse verificata.
In JML è possibile definire separatamente la postcondizione che vale nel caso in cui il metodo esegua regolarmente dalle postcondizioni che valgono nel caso in cui durante l'esecuzione del metodo si verifichino delle eccezioni.
La prima si esplicita attraverso il blocco `ensures`.
La seconda attraverso `signals (<tipo eccezione> e)`.
Nel caso in cui la postcondizione sia `true` il metodo non garantisce nessun "effetto" al termine della sua esecuzione, quindi può "fare ciò che vuole": non c'è motivo di omettere la postcondizione.

<!-- TODO:
 - assertions (di secondaria importanza)  -->

## Astrazione procedurale

Si dice **astrazione procedurale** la specifica di un'operazione (anche complessa) definita su un dominio di dati generici (parametri).
In Java coincide con la specifica (ad esempio attraverso la notazione JML) di un metodo statico.
Infatti un metodo statico rappresenta proprio un'operazione "priva di stato": il suo comportamento non dipende dai valori di attributi non statici, ma è determinato unicamente dai parametri.

## ADT: Abstract Data Type

Si dice **abstract data type** (o **ADT**) un tipo di dato per cui tutti gli stati ammissibili e le operazioni che vi si possono effettuare (includendo il modo in cui quest'ultime permettono di passare da uno stato all'altro) sono descritti attraverso una specifica.
La specifica di un ADT si compone di una sintassi e di una semantica.
La sintassi coincide con l'interfaccia del tipo di dato in questione (l'insieme di metodi pubblici che espone). Per definire la semantica in maniera esaustiva occorre utilizzare un linguaggio di specifica formale come JML.
A differenza dell'astrazione procedurale, nello specificare un ADT con JML, dobbiamo trattare anche le transizioni di stato dell'oggetto dovute alle varie operazioni (cioè dire ciò che cambia, come cambia e cosa invece rimane invariato tra i valori che rappresentano lo stato dell'oggetto a seguito dell'esecuzione di un certo metodo).

### Metodi puri

Un metodo **di un ADT** si dice **puro** se:
 - vale `//@ assignable \nothing;`
 - gli unici metodi che invoca sono anche essi puri
 - non modifica nessun attributo (pubblico o privato) dell'ADT

I metodi puri si indicano in JML con la keyword `/* @ pure @ */`.
Ad esempio, supponiamo che il metodo `dimensione` restituisca la cardinalità di un ADT che rappresenta una collezione di oggetti.
`dimensione` è chiaramente un metodo puro, in quanto non modifica lo stato della collezione, per esplicitarlo in JML possiamo usare la sintassi: `public int /* @ pure @ */ dimensione();`.

Anche un costruttore può essere **puro** se si limita ad inizializzare gli attributi dell'oggetto senza apportare altre modifiche.

I metodi puri si dicono anche **observer** in quanto permettono di "osservare" lo stato di un ADT in un determinato momento.

### Classi pure

Una classe i cui metodi **pubblici** (e costruttori) sono tutti **puri** si dice **pura** e si indica con la sintassi:
`public /* @ pure @ */ class NomeClasse`.
Una classe **pura** è una classe **immutabile**.

**Attenzione**: quando specifichiamo che una classe è **pure** **NON** è necessario che nella specifica si espliciti che il suo stato non cambia (cioè che tutti gli observer restituiscono gli stessi risultati prima e dopo l'esecuzione del metodo).
Questo risulterà utile in seguito per alleggerire la specifica in JML dei metodi.

### Specifica di un'operazione di un ADT in JML

Valgono le regole sintattiche e semantiche già introdotte per JML.
La struttura della specifica rimane quella usuale.

---

**Attenzione**: quando specifichiamo un'operazione di un ADT in JML, nella specifica possono comparire solo gli altri metodi (e attributi) **pubblici** e **puri** (dell'ADT), i parametri formali dell'operazione (su cui possiamo invocare i rispettivi metodi **pubblici** e **puri**) e `\result` per fare riferimento al risultato restituito.

### Esempio

Vediamo un esempio di ADT.

Vogliamo descrivere attraverso la specifica un _insieme (mutabile) di interi_ su cui sono definite le seguenti operazioni:
- _costruzione_: crea ed inizializza l'insieme come un insieme vuoto
- _inserisci(x)_: aggiunge l'elemento x all'insieme
- _rimuovi(x)_: rimuove l'elemento x dall'insieme
- _appartiene(x)_: restituisce _vero_ se x appartiene all'insieme, _falso_ altrimenti
- _cardinalità_: resituisce la cardinalità dell'insieme
- _scegli_: restituisce uno tra gli elementi dell'insieme

Alcuni valori ammissibili per l'insieme sono: _{1, 10, 35}_, _{7}_, ...

```java
public class InsiemeDiInteri {
  // OVERVIEW: Insieme di interi illimitato
  //  e mutabile
  
  // Observer:

  //@ ensures (* \result equivale a
  //@ "x appartiene all'insieme" *);
  public /* @ pure @ */
    boolean appartiene(int x);

  //@ ensures \result ==
  //@   (\num_of int x; ; appartiene(x))
  public /* @ pure @ */ int cardinalita();

  //@ ensures appartiene(\result) &&
  //@ cardinalita() > 0;
  //@ signals (EccezioneInsiemeVuoto e)
  //@ cardinalita() == 0;
  public /* @ pure @ */ int scegli()
    throws EccezioneInsiemeVuoto;

  // Creator:

  //@ ensures cardinalita() == 0;
  public InsiemeDiInteri();

  // Mutator:

  //@ ensures appartiene(x) &&
  //@ cardinalita() == \old(cardinalita() +
  //@   (appartiene(x) ? 0 : 1)) &&
  //@ (\forall int y; \old(appartiene(y));
  //@   appartiene(y));
  public void inserisci(int x);

  //@ ensures !appartiene(x) &&
  //@ cardinalita() == \old(cardinalita() -
  //@   (appartiene(x) ? 1 : 0)) &&
  //@ (\forall int y; appartiene(y);
  //@   \old(appartiene(y)));
  public void rimuovi(int x);
}
```

Osserviamo che **NON** tutti i metodi pubblici dell'oggetto possono essere specificati formalmente (ovvero senza dover ricorrere ai commenti) in JML. Questo in particolare è vero per alcuni degli **observer**, nel caso d'esempio: `appartiene`.
Per poter specificare formalmente questi metodi sarà necessario dichiarare un **rappresentante**, cioè un oggetto che realizza lo stato concreto dell'ADT, (spiegato in seguito) e fare riferimento all'implementazione.

Un ADT deve consentire di utilizzare gli oggetti che descrive, senza conoscerne l'implementazione. Vediamo come implementare, conoscendo solo la specifica, un metodo che crea un `InsiemeDiInteri` a partire da un array di interi:
```java
public static InsiemeDiInteri daArray(int[] a)
  throws NullPointerException {
  
  if (a == null) {
    throw new NullPointerException();
  }

  InsiemeDiInteri s = new InsiemeDiInteri();
  // Dalla specifica s è vuoto

  for (int x : a) {
    s.inserisci(x);
  }
  // Dalla specifica s contiene tutti
  // e soli gli interi (x) in a

  return s;
}
```

### Categorie di operazioni

Possiamo classificare le operazioni (i metodi pubblici) definite su un ADT nelle seguenti categorie:
- **_Creator_**: creano un nuovo oggetto del tipo definito dall'ADT prendendo in input parametri che **NON** sono altri oggetti del tipo definito dall'ADT
- **_Producer_**: creano un nuovo oggetto del tipo definito dall'ADT prendendo in input un oggetto del tipo definito dall'ADT
- **_Mutator_**: modificano lo stato dell'oggetto
- **_Observer_**: restituiscono un risultato di un tipo diverso da quello definito dall'ADT; solitamente non modificano l'oggetto e quindi sono dichiarati come puri

Un tipo _mutabile_ "adeguato" dovrebbe disporre di _creator_, _observer_ e _mutator_.

Un tipo _immutabile_ "adeguato" dovrebbe disporre di _crator_, _observer_ e _producer_.

### Proprietà astratte (evolutive e invarianti)

Si dicono proprietà **astratte** di un ADT tutte le proprietà di cui esso gode, che sono deducibili dalla specifica dei suoi metodi pubblici.
Si distinguono in:
- Proprietà **evolutive**: specificano la relazione tra uno stato osservabile ed il successivo (ovvero specificano come l'oggetto evolve). Un esempio di proprietà evolutiva è l'immutabilità, che può essere espressa attraverso il concetto di stato corrente e successivo come segue: "Per ogni stato corrente dell'oggetto, per ogni operazione, detto stato successivo lo stato in cui si trova l'oggetto dopo aver eseguito l'operazione, lo stato corrente coincide con lo stato successivo"

---

- Properità **invarianti**: si tratta di proprietà che sono valide per qualunque stato ammissibile dell'oggetto. Nell'esempio `InsiemeDiInteri`, una proprietà invariante è: `cardinalita() >= 0`.

Le proprietà **evolutive** **NON** sono **rappresentabili direttamente in JML**: non esiste una sintassi per dichiararle esplicitamente, ma seguono dalle specifiche dei singoli metodi.

Al contrario, per **rappresentare in JML** una proprietà **invariante**, anche detta **invariante pubblico**, si usa la seguente sintassi:
```java
public class ClasseADT {
  //@ public invariant <condizione>;

  ...
}
```

Le proprietà astratte permettono agli utenti dell'ADT di fare assunzioni che ne semplificano l'utilizzo.

#### Dimostrare la validità di un invariante pubblico

Dichiarare un invariante pubblico non è sufficiente per garantirne la validità.
Dobbiamo assicurarci, attraverso la specifica, che l'invariante sia valido per tutti gli stati "iniziali" delle istanze dell'ADT: ovvero gli oggetti ottenuti invocando i creator. Successivamente è necessario verificare che, a partire da un generico stato ammissibile dell'oggetto, applicando una qualsiasi delle operazioni definite e assumendo vere le rispettive precondizioni, la proprietà sia ancora valida.
In particolare uno stato si considera "ammissibile" se è raggiungibile applicando un nunmero finito di volte le operazioni dell'ADT ad uno degli stati iniziali.
Non è necessario dimostrare che gli observer soddisfino l'invariante, dato che non modificano lo stato dell'oggetto.

### Rappresentante

Per **implementare** un ADT è necessario dichiarare un **rappresentante** (o **`rep`**), ovvero una _struttura dati_ in grado di rappresentare, attraverso i valori che assume, lo stato concreto dell'ADT.
In Java questo si traduce in un insieme di attributi **privati**.
Ricordiamo che l'utente deve poter utilizzare l'ADT conoscendo esclusivamente la sua specifica, quindi non è necessario (anzi vedremo essere una pratica scorretta) esporre il rappresentante dello stato concreto (magari dichiarandolo pubblico).

Nell'esempio `InsiemeDiInteri` un rappresentante molto semplice, ma efficace, è un `ArrayList<Integer>` che contiene gli elementi dell'insieme.
Vediamo una possibile implementazione:
```java
public class InsiemeDiInteri {
  private ArrayList<Integer> rep;

  public boolean appartiene(int x) {
    return trova(x) != -1;
  }

  public int cardinalita() {
    return rep.size();
  }

  public int scegli() throws
      EccezioneInsiemeVuoto {
    if (rep.size() == 0) {
      throw new EccezioneInsiemeVuoto();
    }
    return rep.get(0);
  }

  public InsiemeDiInteri() {
    rep = new ArrayList<>();
  }

  public void inserisci(int x) {
    if (appartiene(x)) { return; }
    rep.add(x);
  }

  public void rimuovi(int x) {
    int iX = trova(x);
    if (iX == -1) { return; }
    rep.remove(iX);
  }

  // trova è un metodo di ausilio che cerca
  // x in rep e, se lo trova
  // restituisce l'indice corrispondente,
  // altrimenti -1
  private /* @ helper @ */ int trova(int x) {
    for (int i = 0; i < rep.size(); i++) {
      if (rep.get(i) == x) { return i; }
    }
    return -1;
  }
}
```

### Funzione di astrazione

Si dice **funzione di astrazione** (o **AF**) una funzione (in senso matematico) che associa ad ogni stato concreto ammissibile, rappresentato dal `rep`, lo stato astratto (dell'ADT) che vi corrisponde.
Nell'esempio `InsiemeDiInteri` lo stato concreto è un `ArrayList<Integer>` come ad esempio `[4, 1, 2, 3]`. L'AF associa `[4, 1, 2, 3]` all'insieme `{1, 2, 3, 4}` che è proprio lo stato astratto dell'ADT corrispondente a tale `ArrayList`.
Le funzioni di astrazione possono risultare più o meno complicate e **dipendono** dall'implementazione scelta.
Solitamente sono **NON** iniettive: più stati concreti corrispondono allo stesso stato astratto. Nell'esempio `[4, 1, 2, 3]` e `[1, 2, 3, 4]` corrispondono entrambi all'insieme `{1, 2, 3, 4}`.

#### Come dichiarare l'AF in JML

In JML è possibile **dichiarare** (**NON** implementare) la funzione di astrazione attraverso la seguente sintassi:
```java
public class ClasseADT {
  ...
  // AF:
  //@ private invariant
  //@ <condizione>;
  ...
}
```
L'AF viene dichiarata all'interno del blocco JML **private invariant**, che ci consente di accedere, oltre che agli attributi e metodi pubblici della classe, **anche a quelli privati**.
Nella condizione JML siamo interessati ad esplicitare la **relazione** (logica) che sussiste tra lo stato concreto e lo stato astratto corrispondente dell'ADT. Cioè non vogliamo spiegare cosa la funzione fa (la sua implementazione) ma solo le proprietà che devono valere perchè uno stato concreto ed uno astratto siano corrispondenti.

---

Nell'esempio `InsiemeDiInteri` con un'`ArrayList` come `rep`, a prescindere da come l'AF venga realizzata, vale che _"un elemento `x` appartiene all'insieme s (stato astratto) sse esiste un indice i compreso tra 0 e `rep.size()` tale che `rep.get(i) == x` (stato concreto)"_.
Lo stato concreto è rappresentato dal `rep`, a cui possiamo accedere dato che è costituito da un insieme di attributi privati (ricordiamo che siamo nel private invariant). 
Lo stato astratto invece non è realmente memorizzato da nessuna parte, è possibile accedervi solo attraverso gli _observer_.
Quindi nella condizione JML compariranno gli attributi **privati** che costituiscono il `rep` ed gli _observer_ che permettono di osservare lo stato astratto dell'ADT, legati tra loro attraverso delle formule logiche che risultano vere solo quando i valori assunti dagli attributi **privati** corrispondono con lo stato astratto osservato.
Dichiariamo l'AF nell'esempio `InsiemeDiInteri`:
```java
public class InsiemeDiInteri {
  ...
  // AF:
  //@ private invariant
  //@ (\forall int x; ;
  //@   appartiene(x) <==>
  //@   (\exists int i; 0 <= i &&
  //@     i < rep.size(); rep.get(i) == x));
  ...
}
```

Notiamo che siamo finalmente riusciti a specificare formalmente il metodo `appartiene` che, prima dell'introduzione del `rep`, era semplicemente descritto attraverso un commento in JML.

#### Come implementare l'AF

Per **implementare** l'AF solitamente si ricorre ad una rappresentazione testuale (tramite una stringa) degli stati astratti, quindi si ridefinisce `toString`.
Nell'esempio `InsiemeDiInteri` una possibile implementazione dell'AF (attraverso i paradigmi della programmazione funzionale) è quella che segue:
```java
public class InsiemeDiInteri {
  ...
  @Override
  public String toString() {
    return rep.stream().sorted()
      .map(x -> x.toString())
      .collect(Collectors
        .joining(", ", "{", "}"));
  }
}
```
Osserviamo che l'ordinamento della lista di interi prima della stampa fa in modo che gli stati astratti corrispondenti a `[1, 2, 3, 4]` e `[4, 3, 2, 1]`, **che sono uguali**, siano rappresentati da un'unica stringa `"{1, 2, 3, 4}"`.

### Invariante di rappresentazione

**NON** tutti gli stati concreti assunti dal `rep` sono rappresentanti ammissibili di uno stato astratto.
Nell'esempio `InsiemeDiInteri` risulta evidente che i seguenti valori per il `rep` **NON** costituiscano degli stati ammissibili:
- `null`
- `[1, null, 3]`

Ci sono però altre assunzioni (implicite) che facciamo nell'implementazione di `InsiemeDiInteri` che rendono inammissibili anche altri stati concreti che potrebbero sembrare validi.
Ad esempio, quando rimuoviamo un elemento dall'insieme, rimuoviamo dal `rep` al più un elemento (in particolare rimuoviamo l'elemento che vale `x` con indice minimo, se esiste). Quindi, perché l'implementazione funzioni correttamente, è imperativo che nel `rep` non compaiano duplicati (altrimenti la rimozione non rimuoverebbe tutti gli elementi uguali ad `x`). Dunque, ad esempio, anche `[1, 1, 2]` è uno stato concreto inammissibile.

L'**invariante di rappresentazione** (o **RI**) è una proprietà invariante, che quindi deve essere verificata in **tutti** gli stati osservabili dell'istanza dell'ADT (questo punto in particolare sarà chiarito in _Validità e conservazione dell'RI_), privata, cioè che fa riferimento **esclusivamente** agli attributi privati della classe, in particolare a quelli che costituiscono il `rep`, che deve essere soddisfatta perchè lo stato concreto rappresentato dal `rep` sia ammissibile.
Analogamente si può definire l'RI come la proprietà che permette di discernere tra i valori del `rep` che appartengono al dominio della funzione di astrazione (gli stati concreti ammissibili, per cui esiste uno stato astratto corrispondente) da quelli che non vi appartengono (gli stati concreti inammissibili, per cui non esiste uno stato astratto corrispondente e per cui, di conseguenza, la funzione di astrazione risulta indefinita).
Ovviamente l'RI dipende fortemente dalle scelte implementative.

Per dichiarare l'invariante di rappresentazione in JML si usa la seguente sintassi:
```java
public class ClasseADT {
  ...
  // RI:
  //@ private invariant
  //@ <condizione-sul-rep>;
  ...
}
```
Nella condizione in JML sul `rep` compariranno appunto **solo gli attributi** (privati) **che costituiscono il `rep`**. La condizione risulterà vera _sse_ il `rep` rappresenta uno stato concreto ammissibile.

Dichiariamo l'RI di `InsiemeDiInteri`:
```java
public class InsiemeDiInteri {
  ...
  // RI:
  //@ private invariant
  //@ rep != null && !rep.contains(null) &&
  //@ (\forall int i; 0 <= i &&
  //@   i < rep.size() - 1;
  //@   (\forall int j; i < j &&
  //@     j < rep.size();
  //@     !rep.get(i).equals(rep.get(j))));
  ...
}
```

---

#### Validità e conservazione dell'RI

Gli _stati osservabili_, cioè quelli per cui si verifica la validità dell'RI, sono gli stati in cui si trova il `rep` quando nessun metodo **pubblico** è **in esecuzione**. Questo perché, durante l'esecuzione di un metodo, l'invariante di rappresentazione potrebbe essere temporaneamente violato per motivi implementativi per poi essere ripristinato prima della fine dell'esecuzione.

Ad esempio, consideriamo un'implementazione **alternativa** inefficiente di `inserisci` in `InsiemeDiInteri`:

```java
public class InsiemeDiInteri {
  ...
  public void inserisciIneff(int x) {
    int iX = trova(x);
    rep.add(x);
    if (iX != -1) { rep.remove(x); }
  }
  ...
}
```
`inserisciIneff` controlla se `x` sia già un elemento dell'insieme, in caso affermativo lo inserisce in fondo (con `add`) e rimuove il duplicato (con `remove`), altrimenti effettua solo l'inserimento.
Nonostante nel primo scenario, tra la chiamata ad `add` e quella a `remove`, l'RI risulti temporaneamente violato, dato che avremo un elemento `x` duplicato in `rep`; l'implementazione è comunque valida perché ripristina l'invariante prima del termine dell'esecuzione del metodo.

Per verificare che l'RI sia valido e si conservi durante il ciclo di vita dell'oggetto dobbiamo innanzitutto verificare che valga dopo l'esecuzione di tutti i costruttori pubblici (in tutti gli stati concreti iniziali). Poi dobbiamo dimostrare che, supponendo che l'RI sia valido per un certo valore del `rep` (quindi supponendo di trovarci in uno stato concreto ammissibile), per ogni metodo pubblico della classe, al termine dell'esecuzione di tale metodo, l'invariante sia ancora rispettato.

### Esposizione del `rep`

Si parla di **esposizione del `rep`** quando si fornisce all'esterno un riferimento al `rep` dell'ADT.
Si tratta di una pessima pratica di programmazione perché consente agli utilizzatori dell'ADT di violare l'invariante di rappresentazione, agendo direttamente sul riferimento al `rep` di cui dispongono.
Avviene principalmente in due modalità (che appaiono innocue):
- Restituire il `rep` attraverso un metodo pubblico.
Consideriamo l'esempio `InsiemeDiInteri` e supponiamo di voler implementare il metodo `comeArrayList` che restituisce una rappresentazione dell'insieme sotto forma di `ArrayList<Integer>`. Un'implementazione che potrebbe risultare naturale è:
```java
public class InsiemeDiInteri {
  ...
  public ArrayList<Integer> comeArrayList() {
    return rep;
  }
  ...
}
```
**Sbagliato!** Stiamo esponendo il `rep`.
- Assegnare un riferimento ricevuto come parametro al `rep`.
Supponiamo ora di voler implementare il metodo _statico_ `daArrayList` che riceve un `ArrayList<Integer>` e restituisce il corrispondente `InsiemeDiInteri`. Una possibile implementazione è:
```java
public class InsiemeDiInteri {
  ...
  public static InsiemeDiInteri
    daArrayList(ArrayList<Integer> lista) {
    InsiemeDiInteri s = new InsiemeDiInteri();
    s.rep = lista;
    return s;
  }
  ...
}
```
Anche in questo caso l'implementazione è **sbagliata!** Non solo stiamo esponendo il `rep`, non stiamo nenche controllando che `lista` soddisfi l'RI.

Per ovviare a questi problemi di solito si ricorre ai _copy constructor_.
Ad esempio, per evitare l'esposizione del `rep` in `comeArrayList`:
```java
public class InsiemeDiInteri {
  ...
  public ArrayList<Integer> comeArrayList() {
    return new ArrayList<Integer>(rep);
  }
  ...
}
```

## Trucchi per l'esame

_**Attenzione!**: I seguenti "trucchi" sono stati ricavati analizzando pattern ricorrenti nella risoluzione degli esercizi sul JML. **NON** sono algoritmi per risolvere gli esercizi e **NON** garantiscono di trovare la soluzione corretta._

Prima di procedere alla specifica di un metodo in particolare, risulta utile analizzare la classe nel suo complesso.

### Individuare gli _observer "indipendenti"_

Definiamo (è una definizione inventata dagli autori del cheatsheet) **indipendenti** gli _observer_ la cui specifica non può essere espressa in funzione di altri _observer_ della classe (o di altre classi).
Gli _observer indipendenti_ possono essere completamente specificati solo attraverso la funzione di astrazione, facendo riferimento al `rep`.
Per poter applicare le _tecniche_ che seguono è necessario individuare quali sono gli _observer indipendenti_ della classe in analisi: solitamente, nei TdE, si tratta di _observer_ che restituiscono collezioni (`List` o `Set` nella maggior parte dei casi).

Dopo aver letto **attentamente** la specifica informale in linguaggio naturale, procediamo alla specifica del metodo in JML:

### Ricavare la precondizione (`requires`)

- Solitamente nella precondizione si richiede che tutti i parametri in input di tipo riferimento **NON** siano `null`

---

- Nel caso di parametri di tipo numerico, se rappresentano quantità positive o non negative può essere necessario specificarlo nella precondizione

- Nel caso in cui la classe rappresenta una collezione di oggetti, uno dei parametri potrebbe essere un oggetto della collezione ed, a volte, è necessario specificare che vi faccia parte

Vediamo un esempio **per quest'ultimo caso**: l'esercizio 1 del TdE del 2022-06-18.

_Si consideri la classe Java `HotelDB` per gestire la prenotazione di stanze di hotel._
```java
public class HotelDB {
  // Ritorna l’elenco di tutti gli hotel
  // contenuti.
  public /*@ pure @*/ Set<Hotel> getHotels();

  // Ritorna la lista di tutte le stanze che
  // (i) possono ospitare almeno people
  // persone, (ii) si trovano vicino a
  // location, (iii) sono libere il giorno
  // day. La lista e’ in ordine crescente di
  // prezzo (dalla stanza meno costosa alla
  // piu’ costosa).
  public /*@ pure @*/ List<Room>
    findRooms(int people, Location location,
    Day day);

  // Prenota la stanza room per il giorno day.
  // Solleva una AlreadyBookedException se la
  // stanza non e’ disponibile il giorno
  // specificato.
  public void book(Room room, Day day)
    throws AlreadyBookedException;
}

public class Hotel {
  // Ritorna tutte le stanze presenti
  // nell’hotel.
  public /*@ pure @*/ Set<Room> getRooms();
  
  // Ritorna true sse l’hotel e’ vicino a
  // location.
  public /*@ pure @*/ boolean
    isCloseTo(Location location);
}

public class Room {
  // Ritorna true sse la stanza e’ disponibile
  // il giorno day.
  public /*@ pure @*/ boolean
    isAvailable(Day day);
    
  // Ritorna il numero massimo di persone che
  // la stanza puo’ ospitare.
  public /*@ pure @*/ int getMaxPeople();

  // Ritorna il prezzo della stanza.
  public /*@ pure @*/ float getPrice();

  // Permette di prenotare la stanza nel
  // giorno precisato. Richiede che la stanza
  // non sia gia’ prenotata per lo stesso
  // giorno.
  public void book(Day day);
}
```
Nel punto _b_ dell'esercizio viene chiesto di specificare il metodo `book` di `HotelDB`.
Il metodo `book` ha tra i suoi parametri `room` ovvero la stanza da prenotare; nella precondizione dobbiamo specificare che la stanza in questione si trovi in uno degli hotel nel nostro database:
```java
//@ requires room != null && day != null &&
//@ (\exists Hotel h; getHotels()
//@   .contains(h); h.getRooms()
//@   .contains(room));
//@ ...
public void book(Room room, Day day)
  throws AlreadyBookedException;
```

**Attenzione!**: a volte il metodo che stiamo specificando restituisce delle eccezioni quando uno dei parametri ha dei valori non ammessi (può succedere per tutti i casi elencati); in tal caso **NON** bisogna specificare nella precondizione che il parametro abbia un valore ammissibile: ce ne occuperemo nei blocchi `ensures` e `signals`.

Ricordarsi sempre di leggere **attentamente** la specifica informale in linguaggio naturale, dove potrebbero essere segnalate altre precondizioni particolari, ad hoc per il metodo in questione. 

### Classificare il metodo

Per semplificare la stesura della specifica in JML risulta conveniente differenziare il tipo di metodo che dobbiamo specificare (vedi il paragrafo _Categorie di operazioni_) nelle seguenti categorie:
- _Mutator che non restituiscono nulla_
- _Observer puri_
- _Mutator che restituiscono qualcosa_
- _Creator_
- _Producer in classi pure (immutabili)_

### Ricavare la postcondizione normale (`ensures`)

**Oltre** a ciò che è espresso nella specifica informale in linguaggio naturale, nella specifica formale in JML dobbiamo esplicitare ulteriori condizioni che dipendono dalla categoria del metodo individuata nel punto precedente.
**Attenzione!**: se il metodo in questione lancia un'eccezione, nel blocco `ensures` dobbiamo specificare che **NON** si è verificata la condizione eccezionale.

- #### _Mutator che non restituiscono nulla_

Per definizione, nel caso di esecuzione "normale" (senza eccezioni), un _mutator_ modifica lo stato degli oggetti. Dobbiamo assicurarci che ciò che cambia è solo la porzione di stato modificata dal _mutator_; è necessario esplicitare nella specifica che **tutto il resto rimane invariato**. Dato che si tratta di _mutator che non restituiscono nulla_ non occorre specificare il `\result`. In particolare **per ogni _observer indipendente_ `obsInd`** della classe:

> **se `obsInd` permette di osservare la modifica apportata all'oggetto**, dobbiamo specificare che la modifica è avvenuta correttamente (non abbiamo modificato troppo o troppo poco). Vediamo alcune porzioni di specifica ricorrenti (ricordiamo che `obsInd` è un _place holder_ per il nome dell'_observer indipendente_ in questione): (_Continua nella facciata successiva_)

---

> - **Inserire un elemento `el` di tipo `T` in una `Collection<T>`** (come `List<T>`, `Set<T>`, ...):

```java
//@ requires el != null && ...;
//@ ensures obsInd().contains(el) &&
//@   obsInd().size() == \old(obsInd().size()
//@   + obsInd().contains(el) ? 0 : 1)
//@   && obsInd().containsAll(\old(obsInd()))
//@   && ...;
...
```
> - **Rimuovere un elemento `el` di tipo `T` da una `Collection<T>`**:

```java
//@ requires el != null && ...;
//@ ensures !obsInd().contains(el) &&
//@   obsInd().size() == \old(obsInd().size()
//@   - obsInd.contains(el) ? 1 : 0)
//@   && \old(obsInd()).containsAll(obsInd())
//@   && ...;
```

> - **Inserire un elemento `el` di tipo `T` in fondo ad una `List<T>`**:

```java
//@ requires el != null && ...;
//@ ensures obsInd().size() ==
//@   \old(obsInd().size() + 1) &&
//@   obsInd().get(obsInd().size() - 1)
//@     .equals(el) &&
//@   (\forall int i; 0 <= i &&
//@     i < \old(obsInd().size());
//@     obsInd().get(i).equals(\old(obsInd()
//@     .get(i)))) && ...
```

<!-- TODO: Rimuovere un elemento da una List -->
<!-- TODO: Specificare che non conserva l'ordine -->

> **altrimenti, se `obsInd` non permette di osservare la modifica apportata all'oggetto**, dobbiamo specificare che la porzione di stato osservata è rimasta invariata. Vediamo alcune porzioni di specifica ricorrenti:

> - **Specificare che una `Collection<T>` rimane invariata**:

```java
//@ requires ...;
//@ ensures obsInd().size() ==
//@   \old(obsInd().size()) && obsInd().
//@   containsAll(\old(obsInd())) && ...;
```

<!-- TODO: Specificare che una list rimane invariata e conserva l'ordine -->

- #### _Observer puri_

Gli _observer_ **puri** (esplicitati attraverso la keyword `/* @ pure @ */`) per definizione non possono modificare lo stato degli oggetti, quindi non è necessario specificarlo in JML (lo si considera sottinteso).
Dobbiamo focalizzarci sullo specificare correttamente `\result` (gli _observer_ per definizione **NON** sono `void`).
Solitamente se il tipo restituito è un riferimento, bisogna specificare che non sia `null`: `\result != null`.
Notiamo che, se in un TdE ci viene chiesto di specificare un _observer_, questo allora non sarà un _observer indipendente_ (in quanto può essere specificato in funzione di altri _observer_). Quindi per caratterizzare `\result` **faremo riferimento alla specifica informale** e **sfrutteremo gli _observer indipendenti_**.
Vediamo alcune porzioni di specifica ricorrenti:

> - **`\result` è un `Set<T>` di elementi che soddisfano una determinata proprietà** (che sarà necessariamente osservabile tramite gli _observer indipendenti_):

```java
//@ requires ...;
//@ ensures \result != null &&
//@   !\result.contains(null) &&
//@   (\forall T t; ;
//@     \result.contains(t) <==>
//@     <condizione sugli
//@      observer indipendenti>) && ...;
```

> - **`\reuslt` è una `List<T>` di elementi che soddisfano una determinata proprietà**:

Come prima solo che dobbiamo specificare che nella `List` non vi sono duplicati (per i `Set` è sempre garantito)
```java
//@ requires ...;
//@ ensures \result != null &&
//@   !\result.contains(null) &&
//@   (\forall T t; ;
//@     \result.contains(t) <==>
//@     <condizione sugli
//@      observer indipendenti>) &&
//@   (\forall int i; 0 <= i &&
//@     i < \result.size() - 1;
//@     (\forall int j; i < j &&
//@       j < \result.size();
//@       !\result.get(i).
//@       equals(\result.get(j)))) && ...;
```

- #### _Mutator che restituiscono qualcosa_

Osserviamo che per realizzare qualsiasi _mutator che restituisce qualcosa_ è sufficiente invocare prima un _observer_ che ricava il risultato da restituire (facendo riferimento allo stato dell'oggetto prima della modifica ed ai parametri in input, che costituiscono tutto il contenuto informativo a nostra disposizione), salvare ciò che restituisce, invocare un _mutator che non restituisce nulla_ che modifica l'oggetto secondo la specifica ed infine restituire il risultato salvato.
Quindi per specificare un _mutator che restituisce qualcosa_ sarà sufficiente fare riferimento alle tecniche per la specifica relative a _mutator che non restituiscono nulla_ e _observer puri_ e mettere in `&&` le postcondizioni ottenute (facendo sempre attenzione a ciò che si ottiene).

- #### _Creator_

I _creator_ creano un oggetto "dal nulla" (tutti i _creator_ sono costruttori, non vale il viceversa), quindi l'oggetto creato non ha uno stato precedente all'invocazione del metodo. Per questo motivo, a differenza dei _mutator_ non dobbiamo specificare ciò che cambia o ciò che rimane invariato al termine dell'esecuzione. Ci basta che lo stato osservato sia compatibile con la specifica e con i parametri in input. Per farlo è sufficiente, **per ogni _observer indipendente_**, esplicitare che valore restituisce.
Nell'esempio `InsiemeDiInteri`, l'unico _observer indipendente_ è `appartiene`. Da specifica il costruttore di `InsiemeDiInteri`, che è anche un _creator_, inizializza un insieme vuoto, quindi la specifica corrispondente sarà: (_Continua nella facciata successiva_)

---

```java
public class InsiemeDiInteri {
  ...
  //@ ensures !(\exists int x; ;
  //@   appartiene(x));
  public InsiemeDiInteri();
  ...
}
```
In realtà in questo caso possiamo usare un _observer dipendente_ per scrivere una specifica equivalente in maniera più compatta:

```java
public class InsiemeDiInteri {
  ...
  //@ ensures cardinalita() == 0;
  public InsiemeDiInteri();
  ...
}
```

Solitamente nei TdE non viene richiesto di specificare dei _creator_.

- #### _Producer in classi pure (immutabili)_

Dato che la classe che stiamo specificando è **pura** (`public /* @ pure @ */ class ...`), come nel caso degli _observer puri_ non è necessario esplicitare la relazione tra lo stato corrente e quello passato (dire ciò che cambia e ciò che non cambia); rimane sempre tutto invariato.
Stiamo costruendo un nuovo oggetto della stessa classe che stiamo specificando, come nel caso dei _creator_ ne specificheremo lo stato iniziale esplicitando il valore restituito da **ogni _observer indipendente_**. **A differenza dei _creator_** però, **l'oggetto che si trova nello stato iniziale specificato è `\result`**, **NON** `this`. Un'ulteriore differenza è che lo stato iniziale di `\result` non dipende solo dai parametri di input del metodo, ma anche dallo stato dell'oggetto sul quale invochiamo il _producer_ (`this`).
Solitamente nei TdE non viene richiesto di specificare dei _producer_.

### Ricavare la postcondizione eccezionale (`signals`)

- #### _Mutator che non restituiscono nulla_

Quando si verifica un'eccezione durante l'esecuzione di un _mutator_, ci si  aspetta che lo stato dell'oggetto su cui abbiamo invocato il metodo rimanga invariato. Quindi, nella postcondizione nel caso eccezionale, **oltre** a esplicitare cosa ha provocato l'eccezione (facendo riferimento alla specifica informale), specificheremo che lo stato dell'oggetto è rimasto invariato: **per ogni _observer indipendente_** il valore restituito da tale _observer_ è lo stesso di prima che eseguissimo il _mutator_. Possiamo sfruttare le porzioni di specifica ricorrenti introdotte nel paragrafo precedente.

- #### _Observer puri_

Gli _observer puri_ non modificano lo stato dell'oggetto su cui vengono invocati. Nella postcondizione eccezionale è sufficiente esplicitare cosa ha provocato l'eccezione, facendo riferimento alla specifica informale.

- #### _Mutator che restituiscono qualcosa_

Dato che il metodo ha lanciato un'eccezione, il fatto che restituisse qualcosa è irrilevante: ci si comporta come nel caso in cui vogliamo specificare la postcondizione eccezionale di un _mutator che non restituisce nulla_.

- #### _Creator_

Quando un _creator_ fallisce (lancia un'eccezione) non c'è nessuno stato che possiamo osservare: l'oggetto non è stato costruito. È sufficiente specificare cosa ha provocato l'eccezione, facendo riferimento alla specifica informale.

- #### _Producer in classi pure (immutabili)_

Il fatto che la classe sia **pura** implica che lo stato dell'oggetto non possa cambiare: come nel caso degli _observer puri_ è sufficiente esplicitare cosa ha provocato l'eccezione, facendo riferimento alla specifica informale.

<!-- TODO: RI:
Collezioni che contengono liste: liste non nulle e non vuote,
AF, Esempio che usa le tecniche introdotte -->

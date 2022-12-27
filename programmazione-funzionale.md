# Programmazione funzionale

Il paradigma di programmazione funzionale si basa sul principio di considerare le funzioni come oggetti, e quindi utilizzarli come tali. In questo modo, le funzioni possono essere passate come parametri, restituite come risultati, memorizzate in variabili, ecc.
Le funzioni usate come parametro senza specificare il nome della funzione, ma solo il comportamento che essa deve avere, sono dette **funzioni anonime**.

## Espressioni lambda

Supponiamo di avere una classe fatta in questo modo:

```java
class Persona {
  private String nome;
  private int eta;

  public Persona(String nome, int eta) {
    this.nome = nome;
    this.eta = eta;
  }

  public String getNome() {
    return nome;
  }

  public int getEta() {
    return eta;
  }
}
```

e supponiamo di avere una lista di persone: 

```java
List<Persona> persone = new ArrayList<>();
persone.add(new Persona("Mario", 20));
persone.add(new Persona("Luigi", 30));
persone.add(new Persona("Pippo", 40));
persone.add(new Persona("Pluto", 50));
```

Possiamo, ad esempio, ordinare la lista di persone per età, usando il metodo [`sort`](https://docs.oracle.com/javase/8/docs/api/java/util/Collections.html#sort-java.util.List-java.util.Comparator-) della classe `Collections`: 
```java
public static <T> void sort(
  List<T> list, Comparator<? super T> c
)
```

Il metodo `sort` prende come primo parametro una lista di oggetti di tipo `T`, e come secondo parametro un oggetto di tipo `Comparator`, possiamo passare un `Comparator` direttamente usando una **espressione lambda**:

```java
obj.method(
  (param1, param2) -> {
    // corpo della funzione
  }
);
```

Nel nostro esempio il metodo `sort` sarà implementato così:

```java
Collections.sort(persone, (p1, p2) -> {
  /* Java conosce già il tipo di p1 e p2, 
  quindi non è necessario specificarlo */
  if(p1.getEta() > p2.getEta()) {
    return 1; }
  else if(p1.getEta() < p2.getEta()) {
    return -1; }
  else return 0;
});
```

## Interfacce funzionali

Nell'esempio di prima, nel metodo `public static <T> void sort(List<T> list, Comparator<? super T> c)`, il secondo parametro è un oggetto di tipo `Comparator<T>`, è una **interfaccia funzionale**.

Una **interfaccia funzionale** è un'interfaccia che prevede di implementare un solo metodo. In questo caso, l'interfaccia `Comparator<T>` prevede di implementare il metodo `int compare(T o1, T o2)`, che impone un ordine tra due oggetti di tipo `T` e restituisce 1, 0, -1 a seconda che il primo parametro o1 sia rispettivamente maggiore, uguale o minore del secondo.

Avendo l'interfaccia funzionale un solo metodo, possiamo usare direttamente una **espressione lambda** per implementarla:

```java
Comparator<Persona> comparator = (p1, p2) -> {
  if(p1.getEta() > p2.getEta()) {
    return 1; }
  else if(p1.getEta() < p2.getEta()) {
    return -1; }
  else return 0;
};
```

è come se avessimo _"assegnato una funzione ad una variabile (comparator)"_. Possiamo quindi passare la variabile `comparator` come secondo parametro al metodo `sort`: `Collections.sort(persone, comparator);`. Oppure, possiamo passare direttamente una lambda  (come mostrato nel capitolo precedente).

Java fornisce delle `<interfacce funzionali / il corrispondente metodo per eseguire la funzione>` nel package `java.util.function` quali:

- [**`Function<T, R>` / `.apply(T t)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/Function.html#apply-T-): 
  funzione che prende un parametro di tipo `T` e restituisce un oggetto di tipo `R`;
- [**`Consumer<T>` / `.accept(T t)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/Consumer.html#accept-T-): 
  funzione che prende un parametro di tipo `T` e non restituisce nulla;
- [**`Supplier<T>` / `.get()`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/Supplier.html#get--): 
  funzione che non prende parametri e restituisce un oggetto di tipo `T`;
- [**`Predicate<T>` / `.test(T t)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/Predicate.html#test-T-): 
  funzione che prende un parametro di tipo `T` e restituisce un booleano (true o false);
- [**`BiFunction<T, U, R>` / `.apply(T t, U u)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/BiFunction.html#apply-T-U-): 
  funzione che prende due parametri di tipo `T` e `U` e restituisce un oggetto di tipo `R`.

E le corrispondenti per i tipi primitivi `int`, `double` e `long`:

- [**`IntFunction<R>` / `.apply(int v)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/IntFunction.html#apply-int-): 
  funzione che prende un parametro di tipo `int` e restituisce un oggetto di tipo `R`;
- [**`IntConsumer` / `.accept(int v)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/IntConsumer.html#accept-int-): 
  funzione che prende un parametro di tipo `int` e non restituisce nulla;
- [**`IntSupplier` / `.getAsInt()`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/IntSupplier.html#getAsInt--): 
  funzione che non prende parametri e restituisce un oggetto di tipo `int`;

---

- [**`IntPredicate` / `.test(int v)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/IntPredicate.html#test-int-): 
  funzione che prende un parametro di tipo `int` e restituisce un booleano (true o false);
- [**`ToIntFunction<T>` / `.applyAsInt(T v)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/ToIntFunction.html#applyAsInt-T-): 
  funzione che prende un parametro di tipo `T` e restituisce un primitivo di tipo `int`: `int applyAsInt(T value)`;
- [**`DoubleToIntFunction` / `.applyAsInt(double v)`**](https://docs.oracle.com/javase/8/docs/api/java/util/function/DoubleToIntFunction.html#applyAsInt-double-): 
  funzione che prende un parametro di tipo `double` e restituisce un oggetto di tipo `int`...

## Composizione di funzioni (`Stream<T>`)

Possiamo concatenare delle funzioni che agiscono su una Collezione per costruire una **catena di funzioni**, che filtrerà, mapperà e agirà sulla nostra collezione.

Questa catena inizierà invocando il metodo **`stream()`** sulla collezione. Nell'esempio:

```java
Stream<Persona> stream = persone.stream();
```

### `filter`

Possiamo filtrare lo `stream` per far si che tutti gli elementi della collezione soddisfino un certo `Predicate<T>`.
Per farlo, usiamo il metodo [**`Stream<T> filter(<predicato>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#filter-java.util.function.Predicate-). Nel nostro esempio, vogliamo filtrare le persone che hanno più di 30 anni:

```java
Stream<Persona> stream = persone.stream()
  .filter(p -> p.getEta() >= 30);
```

La funzione lambda nel metodo `filter` sarà `true` per tre persone: Luigi, Pippo e Pluto. Verrà quindi eliminato Mario (che ha 20 anni) dal nostro `stream`.

### `map`

[**`Stream<U> map(<funzione da T a U>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#map-java.util.function.Function-) prende in input una funzione (`Function<T, U>`) e la applica ad ogni elemento dello `stream`. Si usa per trasformare gli elementi dello `stream` in altri elementi. Nel nostro esempio, vogliamo trasformare le persone (già filtrate) in stringhe contenenti il nome e l'età:

```java
Stream<String> stream = persone.stream()
  .filter(p -> p.getEta() >= 30)
  .map(p -> {
    return p.getNome() + ": " + 
    p.getEta().toString();
  });
  /* return implicito 
  (valido solo per funzioni 
  con una sola riga) */
```

Otterrò uno `stream`, contenente le stringhe: "Luigi: 30", "Pippo: 40", "Pluto: 50".

Esistono anche metodi simili per mappare a valori primitivi:
[**`IntStream mapToInt(<funzione da T a int>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#mapToInt-java.util.function.ToIntFunction-), 
[**`DoubleStream mapToDouble(<funzione da T a double>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#mapToDouble-java.util.function.ToDoubleFunction-) 
e [**`LongStream mapToLong(<funzione da T a long>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#mapToLong-java.util.function.ToLongFunction-).
Questi ritornano un'istanza di uno stream di valori primitivi, permettendo di chiamare metodi aggiuntivi che possono essere utili (vedi sotto). 

### `distinct` e `sorted`

- [**`Stream<T> distinct()`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#distinct--) 
  elimina gli elementi duplicati dello `stream`.

- [**`Stream<T> sorted()`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#sorted--) 
  ordina gli elementi dello `stream` secondo il loro ordinamento naturale. Funziona solo su tipi che implementano
  già l'interfaccia [`Comparable`](https://docs.oracle.com/javase/8/docs/api/java/lang/Comparable.html) (come ad esempio `Integer` e `String`).

- [**`Stream<T> sorted(Comparator<? super T> c)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#sorted-java.util.Comparator-) 
  ordina gli elementi dello `stream` in base a quanto definito dal `Comparator` dato.

Per facilitare la creazione di `Comparator` esistono anche una serie di metodi, che permettono di mappare oggetti a dei loro campi
per il quale un ordine naturale è già definito (come ad esempio per stringhe e primitivi):
- [**`static <T,U extends Comparable<? super U>> Comparator<T> comparing(Function<? super T,? extends U> keyExtractor)`**](https://docs.oracle.com/javase/8/docs/api/java/util/Comparator.html#comparing-java.util.function.Function-):
  accetta una funzione che estrae un campo dall'oggetto dato e costruisce un comparatore che compara su tale campo.
  Per esempio, il comparatore definito precedentemente (che utilizza l'età delle persone), può essere scritto come:
```java
Comparator<Persona> comparator = 
  Comparator.comparing(p -> p.getEta())
```
- [**`Comparator<T> reversed()`**](https://docs.oracle.com/javase/8/docs/api/java/util/Comparator.html#reversed--):
  Restituisce un comparatore che impone l'ordine inverso di quello corrente. Per esempio, per ordinare una lista di persone
  per età in ordine decrescente:
```java
List<Persona> persone = new ArrayList<>();
persone.add(new Persona("Mario", 20));
persone.add(new Persona("Luigi", 30));
persone.add(new Persona("Pippo", 40));
persone.add(new Persona("Pluto", 50));
Collections.sort(persone, Comparator
  .comparing(p -> p.getEta())
  .reversed());
// persone sarà [Pluto, Pippo, Luigi, Mario]
```
- [**`static <T extends Comparable<? super T>> Comparator<T> naturalOrder()`**](https://docs.oracle.com/javase/8/docs/api/java/util/Comparator.html#naturalOrder--)
  e [**`static <T extends Comparable<? super T>> Comparator<T> reverseOrder()`**](https://docs.oracle.com/javase/8/docs/api/java/util/Comparator.html#reverseOrder--): restituiscono un comparatore di un oggetto T per il quale è già definito un proprio ordine naturale
  che compara in ordine naturale/inverso. Per esempio, per ordinare una lista di interi in ordine decrescente:
```java
List<Integer> a = new ArrayList<>();
a.add(20);
a.add(30);
a.add(40);
a.add(50);
Collections.sort(a, Comparator.reverseOrder());
// a sarà [50, 40, 30, 20]
```

### `flatMap`

[**`Stream<U> flatMap(<funzione da T a Stream<U>>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#flatMap-java.util.function.Function-) prende in input una funzione (`Function<T, Stream<U>>`), la applica ad ogni elemento di tipo T dello `stream`. La funzione restituisce un altro `stream` (in generale contentente elementi di tipo diverso U) per ogni elemento. Infine tutti gli `stream` restituiti dalla funzione vengono concatenati in un unico `stream`.

Nel nostro esempio, vogliamo trasformare ogni persona (sempre filtrata con età >= 30) in una lista di stringhe contenenti il nome e l'età, e poi concatenare tutti gli `stream` in un unico `stream`:

```java
Stream<String> stream = persone.stream()
  .filter(p -> p.getEta() >= 30)
  .flatMap(p -> {
    List<String> listaPerP;
    listaPerP = new ArrayList<>();
    listaPerP.add(p.getNome());
    listaPerP.add(p.getEta().toString());
    return listaPerP.stream();
  });
```

Otterrò uno `stream`, contenente le stringhe: "Luigi", "30", "Pippo", "40", "Pluto", "50".

Esistono anche metodi simili per flat-mappare a valori primitivi:
[**`IntStream flatMapToInt(<funzione da T a IntStream)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#flatMapToInt-java.util.function.Function-), 
[**`DoubleStream flatMapToDouble(<funzione da T a DoubleStream)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#flatMapToDouble-java.util.function.Function-) 
e [**`LongStream flatMapToLong(<funzione da T a LongStream)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#flatMapToLong-java.util.function.Function-).
Questi ritornano un'istanza di uno stream di valori primitivi, permettendo di chiamare metodi aggiuntivi che possono essere utili (vedi sotto). 

### `reduce`

La [**`T reduce(Identità, <funzione binaria>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#reduce-T-java.util.function.BinaryOperator-) è un'operazione di aggregazione che restituisce un singolo valore a partire da uno `stream`. 

Si ha come primo parametro un valore iniziale (identità), e come secondo parametro una funzione binaria che prende in input due elementi dello `stream` e restituisce un altro elemento (dello stesso tipo) ottenuto a partire dai due. La funzione verrà applicata induttivamente ad ogni elemento dello `stream`, fino ad ottenere un solo elemento.

Nel nostro esempio, vogliamo ottenere la somma delle età delle persone (filtrate):

```java
Integer sommaEta = persone.stream()
  .filter(p -> p.getEta() >= 30)
  /* mapToInt è uguale alla map, 
  ma restituisce uno stream di interi */
  .mapToInt(p -> p.getEta())  
  .reduce(
    0, 
    (eta1, eta2) -> eta1 + eta2 );
```

Otterrò un intero: 120. Nelle varie iterazioni nello `stream` contentente le età `[30, 40, 50]`, la `reduce` si applica in questo modo: 

- 0 (valore iniziale) + 30 (primo elemento dello stream) = 30 (risultato parziale), 
- 30 (risultato parziale della iterazione precedente) + 40 (secondo elemento dello stream) = 70, 
- 70 + 50 = 120.

Esiste in aggiunta anche un overload che non richiede un'identità [**`Optional<T> reduce(<funzione binaria>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#reduce-java.util.function.BinaryOperator-). Questo permette di effettuare la medesima operazione di riduzione, sapendo però in aggiunta se lo stream fosse vuoto o contenesse degli elementi:
- Una riduzione come la precedente su `[30, 40, 50]` restituisce ancora 120
- Una riduzione come la precedente su `[0]` restituisce ancora 0
- Una riduzione come la precedente su `[]` restituisce `Optional.empty()` invece di 0

---

### `collect`

Siamo ora interessati ad avere una Collezione (List, Set, ...) invece che uno stream. Per fare ciò, possiamo usare il metodo [**`Collection<T> collect(<funzione che restituisce una Collezione>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#collect-java.util.stream.Collector-). Nel nostro esempio, vogliamo ottenere una lista di stringhe contenente nome: età delle persone (filtrate con età >= 30):

```java
List<String> lista = persone.stream()
  .filter(p -> p.getEta() >= 30)
  .map(p -> 
    p.getNome() + ": " + 
    p.getEta().toString()
  );
  .collect(Collectors.toList());
```

### `min` e `max`

[**`Optional<T> max(Comparator<? super T> c)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#max-java.util.Comparator-)
e [**`Optional<T> min(Comparator<? super T> c)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#min-java.util.Comparator-)
restituiscono rispettivamente l'oggetto massimo o minimo all'interno dello stream (se presente), secondo l'ordine definito dal `Comparator` dato.

```java
// Restituisce la persona più anziana, Pluto
Optional<Persona> piuAnziano = Arrays.asList(
  new Persona("Mario", 20),
  new Persona("Luigi", 30),
  new Persona("Pippo", 40),
  new Persona("Pluto", 50))
  .stream()
  .max(Comparator.comparing(p -> p.getEta()));
```

### `anyMatch`, `allMatch` e `noneMatch`

[**`boolean anyMatch(<predicato>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#anyMatch-java.util.function.Predicate-),
[**`Optional<T> allMatch(<predicato>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#allMatch-java.util.function.Predicate-)
e [**`Optional<T> noneMatch(<predicato>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#noneMatch-java.util.function.Predicate-) 
restituiscono rispettivamente se almeno uno, tutti o nessuno degli elementi dello stream rispetta il predicato;

```java
List<Persona> persone = Arrays.asList(
  new Persona("Mario", 20),
  new Persona("Luigi", 30),
  new Persona("Pippo", 40),
  new Persona("Pluto", 50));
// Restituisce vero, 
// Pippo e Pluto sono abbastanza anziani
boolean any = persone.stream()
  .anyMatch(p -> p.getEta() > 35);
// Restituisce falso, 
// Mario e Luigi sono più giovani
boolean all = persone.stream()
  .allMatch(p -> p.getEta() > 35);
// Restituisce falso, 
// Pippo e Pluto sono più anziani
boolean all = persone.stream()
  .noneMatch(p -> p.getEta() > 35);
```

### `forEach`

Possiamo usare il metodo [**`forEach(<funzione da T a void>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html#forEach-java.util.function.Consumer-) per eseguire una funzione per ogni elemento dello stream. Nel nostro esempio, vogliamo stampare il nome e l'età di ogni persona (filtrata con età >= 30):

```java
persone.stream()
  .filter(p -> p.getEta() >= 30)
  .forEach(p -> 
    System.out.println(p.getNome() + ": "
    + p.getEta().toString()));
```

## `IntStream`, `DoubleStream` e `LongStream`

Esistono delle specializzazioni della classe Stream per i valori primitivi, ottenibili mediante opportune chiamate a un normale stream con `mapToInt`, `flatMapToInt`, etc.

Queste interfacce definiscono metodi aggiuntivi per facilitare le operazioni di aggregazione, quali:
- [**`OptionalDouble average()`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/IntStream.html#average--)
- [**`OptionalInt max()`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/IntStream.html#max--)
- [**`OptionalInt min()`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/IntStream.html#min--)
- [**`int sum()`**](https://docs.oracle.com/javase/8/docs/api/java/util/stream/IntStream.html#sum--)

Per convenienza questi sono scritti solo per IntStream, ma sono uguali per gli altri, basta semplicemente sostituire `int` con `double`/`long` e `OptionalInt` con `OptionalDouble`/`OptionalLong`

## `Optional<T>`, `OptionalInt`, `OptionalDouble` e `OptionalLong`

L'oggetto [**`Optional`**](https://docs.oracle.com/javase/8/docs/api/java/util/Optional.html) è un contenitore per un valore che può essere nullo. È usato per evitare di avere eccezioni di tipo `NullPointerException`.

Esistono anche le specializzazioni per tipi primitivi `OptionalInt`, `OptionalDouble` e `OptionalLong`. Il loro utilizzo è pressoché identico alla normale classe `Optional`.

Possiamo creare un `Optional` con il valore `val` con il metodo `Optional.of(val)`. Oppure con il metodo `Optional.empty()` per creare un `Optional` vuoto (sostituisce il null).

Sono poi disponibili i metodi per lavorare con gli Optional:

- [**`ifPresent(<funzione>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/Optional.html#ifPresent-java.util.function.Consumer-) che applica la funzione in input solo se l'Optional non è vuoto.

- [**`orElse(<val>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/Optional.html#orElse-T-) che restituisce il valore dell'Optional se non è vuoto, altrimenti restituisce il valore `val` in input.

- [**`Optional<U> flatMap(<funzione da T a Optional<U>)`**](https://docs.oracle.com/javase/8/docs/api/java/util/Optional.html#flatMap-java.util.function.Function-) restituisce un `Optional<U>`, applicando la funzione in input solo se l'`Optional` non è vuoto; altrimenti ritorna un `Optional` vuoto.

Facciamo un esempio usando gli `Optional` e i tre metodi visti in precendenza:

```java
Optional<String> opt = Optional.of("ciao");

// Stampa "ciao"
opt.ifPresent(s -> System.out.println(s));

// Stampa "ciao" perché opt non è vuoto
System.out.println(opt.orElse("vuoto"));

/* La funzione in flatMap viene applicata
e restituisce un Optional<String> 
contenente "ciao mondo", 
quindi viene stampato "ciao mondo" 
per effetto della orElse */
System.out.println(
  opt .flatMap(
    s -> Optional.of(s + " mondo"))
  .orElse("vuoto"));


Optional<String> opt2 = Optional.empty();

// Non stampa nulla perché opt2 è vuoto
opt2.ifPresent(s -> System.out.println(s));

// Stampa "vuoto" perché opt2 è vuoto
System.out.println(opt2.orElse("vuoto"));

/* La funzione in flatMap non viene applicata
e restituisce un Optional<String> vuoto, 
quindi viene stampato "vuoto" 
per effetto della orElse */
System.out.println(
  opt2.flatMap(
    s -> Optional.of(s + " mondo"))
  .orElse("vuoto"));
```

Otterremo in output:
```bash
  ciao
  ciao
  ciao mondo
  vuoto
  vuoto
```

## Closures

Viene detta closure la combinazione di una funzione insieme a una referenza allo stato che
la circonda. 

Detto in maniera diversa, data una funzione lambda, si dice che questa "si chiuda attorno"
(ovvero catturi) le variabili all'interno del suo scope di definizione, permettendo di 
utilizzarle all'interno della lambda stessa.

Con un esempio:
```java
final String prefix = "Z";
Predicate<String> pred = s -> 
    s.startsWith(prefix);
```
la lambda `pred` cattura la variabile prefix, utilizzandola al suo interno, prendendo
quindi il nome di closure.

Per evitare effetti collaterali (*side effects*), viene consentito di catturare solo variabili
`final` oppure **effectively final**, ovvero non dichiarata final ma usata come se fosse tale.
```java
String prefix = "Z";
// Altre istruzioni che fanno cose
String nonFinalPrefix = prefix + "aaaa";
System.out.println(nonFinalPrefix);
nonFinalPrefix = "";
// prefix non è dichiarata final, ma non è 
// mai modificata: è effectively final
Predicate<String> pred = s -> 
    s.startsWith(prefix);
// Errore di compilazione: nonFinalPrefix é 
// modificata, quindi non è effectively final
Predicate<String> pred2 = s -> 
    s.startsWith(nonFinalPrefix);
```

---

<!-- _class: una -->

## Esercizio sulla programmazione funzionale (TdE del 2019-02-18, esercizio 4 - punto c)

### Testo dell'esercizio

Si consideri il seguente metodo statico, che ha la precondizione che ciascun elemento di nums è una stringa corrispondente a una rappresenatazione testuale di un numero intero

```java
public static List<Integer> addX(List<String> nums, int x) {
  List<Integer> plusX = new LinkedList<>();
  for(String numString : nums) {
    number = Integer.valueOf(numString);
    if (number>0)
      plusX.add(number + x);
  }
  return plusX;
}
```

Si riscriva il metodo utilizzando i costrutti della programmazione funzionale di Java 8.

### Soluzione

Il metodo `addX` non fa altro che prendere in input una lista di stringhe `nums` e un intero `x`, e restituire una lista di interi ottenuta sommando `x` a tutti gli interi positivi presenti in `nums` (gli interi <= 0 nella lista `nums` non vengono aggiunti nella lista `plusX`).

Quindi possiamo: 
- applicare il metodo `stream()` alla lista di stringhe per iniziare la nostra "catena di funzioni",
- convertire ogni stringa della lista di partenza in un intero (ritornando poi lo `stream` di interi), tramite una `map` con parametro parametro il metodo `Integer.valueOf(numString)`, 
- filtrare gli interi positivi, 
- sommare `x` a ciascuno di essi.

```java
public static List<Integer> addX(List<String> nums, int x) {
  return nums.stream()
    .map(numString -> Integer.valueOf(numString))
    .filter(number -> number > 0)
    .map(number -> number + x)
    .collect(Collectors.toList());
}
```

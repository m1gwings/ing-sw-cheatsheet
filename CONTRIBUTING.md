# Come contribuire al progetto

## Prerequisiti

Per poter contribuire al progetto è necessario installare i seguenti tool:

- [node.js](https://nodejs.org) (vanno bene entrambe le versioni disponibili: LTS e Current)
- [Github CLI](https://cli.github.com/manual/installation) o, alternativamente, [Github Desktop](https://docs.github.com/en/desktop/installing-and-configuring-github-desktop/installing-and-authenticating-to-github-desktop/installing-github-desktop) (si tratta di un'interfaccia grafica con le funzionalità di Github CLI)
- [git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git) (quest'ultimo è già presente nella maggior parte delle distribuzioni di Linux)

Il primo è un runtime di JavaScript che permette di eseguire lo script (`esporta.js`) che converte il Markdown in un PDF pronto per essere stampato; gli altri sono necessari per creare e gestire la propria copia del progetto (sia in locale che su Github) e poter proporre modifiche all'originale tramite le pull request.

In seguito spiegheremo come utilizzare i tool, sia nel caso abbiate installato Github CLI, che nel caso abbiate installato Github Desktop.

## Con Github CLI

### Autenticazione

Per prima cosa sarà necessario effettuare il login (con le vostre credenziali di Github) su Github CLI attraverso il seguente comando.

```bash
gh auth login
```

Vi si presenteranno dei menù a scelta multipla, quando verrà richiesto il sito su cui autenticarvi selezionate Github.com.
Successivamente, per semplicità, consigliamo di scegliere il login attraverso web browser.

Seguite il processo di login inserendo i dati richiesti.

Quando sarà richiesto quale protocollo scegliere come default, consigliamo HTTPS.

### Fare una fork della repository

Una volta configurati correttamente i tool, vogliamo effettuare una fork del progetto: una repository clonata che apparirà sul vostro profilo Github e che sarà scaricata anche in locale.

Spostatevi nella cartella dove intendete scaricare il progetto.
Ad esempio:

```bash
cd ~/Progetti
```

La seguente operazione creerà la cartella `ing-sw-cheatsheet` all'interno della cartella dove vi siete posizionati. Forkiamo la repository:
```bash
gh repo fork m1gwings/ing-sw-cheatsheet --clone
```
L'opzione `--clone` specifica che non solo volete creare una copia del progetto sul vostro account Github, ma che volete scaricare questa copia anche in locale.

### Installazione delle librerie necessarie

Spostatevi all'interno della nuova cartella creata:
```bash
cd ing-sw-cheatsheet
```

Per poter testare lo script di esportazione è necessario installare le libreria che utilizza, sarà sufficiente lanciare il comando:
```bash
npm i
```

### Esportazione del PDF

Siamo pronti per l'esportazione.
Lanciate lo script:
```bash
node esporta.js
```

Al termine dell'esecuzione il file `cheatsheet.pdf` dovrebbe comparire all'interno della cartella. Complimenti! Avete esportato il PDF con successo.

### Modificare il progetto

Prima di iniziare a modificare il progetto occorre creare un nuovo branch: questo vi permetterà di poter aggiornare periodicamente la storia del branch principale (`main`) senza che ciò su cui state lavorando (all'interno del vostro branch) ne risenta.

Ciascun branch ha un nome, chiamate il nuovo branch descrivendo il contenuto che volete aggiungere, ad esempio: `design-pattern-strategy`.
Per creare un branch si utilizza il seguente comando:
```bash
git checkout -b <nome-branch>
```

Il nuovo branch è stato creato solo sulla copia locale della vostra repository; per salvare le modifiche su Github ed evitare di poterle perdere è necessario creare il branch anche in remoto:
```bash
git push -u origin <nome-branch>
```

Quando ritenete di voler salvare nella storia della repository (sulla **vostra** copia del progetto, sia in locale che in remoto) le modifiche che avete apportato sarà necessario effettuare un commit.
Innanzitutto occorre specificare quali dei file che avete modificato volete salvare, a meno che non abbiate aggiunto dei file senza uno scopo all'interno della cartella (consigliamo di evitarlo), potete specificare di voler salvare tutti i file:
```bash
git add .
```

Siamo pronti per salvare:
```bash
git commit
```

Ora vi si aprirà il vostro text editor di default da terminale. La prima riga che vi scriverete sarà il titolo del commit, le righe successive costituiranno la descrizione. Cercate di specificare brevemente ma in maniera esaustiva le modifiche apportate (sia tramite il titolo, che con la descrizione). Una volta terminato dovete uscire dal text editor, purtroppo questa operazione si effettua in modo diverso a seconda del text editor e noterete che risulta molto più complicata di quello che dovrebbe essere.

Elenchiamo due metodi che funzionano rispettivamente per `vi` e `nano`:
- `vi`: Premete `Esc` e provate ad inserire `:wq` e premere invio (dopo aveer premuto `Esc` se il text editor che state usando è effettivamente `vi`, il cursore si dovrebbe spostare in basso, nella barra dove si inseriscono i comandi)
- `nano`: Premete `Ctrl + x`

Ora dovremo salvare le modifiche apportate alla storia del vostro branch su Github:
```bash
git push
```

### Mantenere la propria copia aggiornata

Mentre lavorate alla vostra modifica, altri contributors potrebbero modificare il progetto principale. Per mantenere aggiornata la vostra versione del progetto utilizzate i seguenti comandi.

Per controllare se vi sono state modifiche:
```bash
git fetch
```

Per scaricare le eventuali modifiche:
```bash
git pull
```

Per le motivazioni spiegate precedentemente, l'unico branch su cui potreste trovare delle modifiche è il `main`, il vostro branch rimarrà inalterato.

### Aprire una pull request

Una volta che la modifica che volevate apportare è stata completata, è il momento di proporla perchè venga aggiunta al progetto originale. Per fare questo apriremo una pull request.

Prima però è bene aggiornare il branch `main`, come spiegato in precedenza, e cercare di minimizzare i conflitti con il branch su cui avete lavorato. Il seguente comando cercherà di apportare le modifiche del vostro branch (fatte a partire da quando l'avete creato) all'ultima versione del `main`:
```bash
git rebase main
```

Il comando potrebbe segnalare dei conflitti nel caso in cui abbiate lavorato su un file che è stato anche modificato nel `main`. Se non siete molto familiari con `git`, annullate l'operazione ed aprite direttamente la pull request senza risolvere i conflitti, ce ne preoccuperemo noi in fase di accettazione.

Nel caso in cui abbiate effettuato l'operazione di rebase con successo, dovrete (come al solito) aggiornare anche la vostra copia in remoto. Controllate prima che il lavoro fatto non sia andato perso. Una volta che vi siete assicurati di ciò, dovrete sovrascrivere la storia del vostro branch in remoto; dopo aver effettuato il rebase le due store sono incompatibili:
```bash
git push -f
```

Possiamo finalmente aprire la pull request:
```bash
gh pr create
```
Selezionate nel menù la `repository m1gwings/ing-sw-cheatsheet`; poi potete premere invio ripetutamente per skippare la compilazione degli altri campi e lasciare i valori di default.

### Cancellare il branch relativo ad una modifica

Una volta che la pull request è stata accettata potete cancellare il branch che avevate creato appositamente per la modifica (la modifica ora è disponibile sul main). Prima di tutto tornate sul branch `main`:
```bash
git checkout main
```

Ora cancellate il branch relativo alla modifica:
```bash
git branch -d <nome-branch>
```
Se non ricordate il nome del branch, il comando `git branch` mostra una lista di tutti i branch della repository.

E cancellatelo anche da Github:
```bash
git push origin --delete <nome-branch>
```

### Passare alla prossima modifica

Ogni volta che volete aggiungere una modifica dovete ripetere il procedimento descritto a partire dalla creazione del branch.
**Ricordate di aggiornare il main (per semplificare il rebase) e di creare il nuovo branch dopo esservi posizionati sul main con `git checkout main`**.

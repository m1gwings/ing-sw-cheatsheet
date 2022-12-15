# Come contribuire al progetto

## Prerequisiti

Per poter contribuire al progetto è necessario installare i seguenti tool:

- [node.js](https://nodejs.org) (vanno bene entrambe le versioni disponibili: LTS e Current)

TODO: git va sempre installato

- [Github CLI](https://cli.github.com/manual/installation) e [git](https://git-scm.com/book/en/v2/Getting-Started-Installing-Git) (quest'ultimo è già presente sulle distribuzioni di linux) o, alternativamente, [Github Desktop](https://docs.github.com/en/desktop/installing-and-configuring-github-desktop/installing-and-authenticating-to-github-desktop/installing-github-desktop) (si tratta di una GUI che integra le funzionalità di entrambi Github CLI e git)


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

###

<!-- - Installare node.js
- Installare Github CLI
- Installare git
- Fare l'autenticazione su Github CLI
- Vai nella cartella progetto
- gh repo fork m1gwings/ing-sw-cheatsheet --clone
- Vai nella cartella
- npm i
- Proviamo esportazione
- node esporta.js
- Creiamo nuovo branch per la feature
- git checkout -b prova-pull-request
- Pushare il branch
- git push -u origin <branch-name>
- Dopo aver lavorato, fare pull request sul sito
- git add .
- git commit
- Premere esc e poi digitare :wq
- git push
- gh pr create (selezionare la repository m1gwings, premere invio per skippare)
- Fare submit
- Se la pull request viene accettata:
- Cancellare il branch dal sito di GitHub
- git branch -d nomeDelBranchLocale
- git push origin --delete nomeDelBranchRemoto -->

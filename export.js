import { Marpit } from '@marp-team/marpit'
import markdownItContainer from 'markdown-it-container'
import fs from 'fs'
import puppeteer from 'puppeteer'

const percorsoFileIndice = 'indice.json'
const percorsoFileStile = 'style.css'
const percorsoFileOutput = 'cheatsheet.pdf'

const marpit = new Marpit().use(markdownItContainer, 'columns')

const tema = fs.readFileSync(percorsoFileStile, 'utf-8')
marpit.themeSet.default = marpit.themeSet.add(tema)

let markdown = `---

marp: true
paginate: true

---

# Cheatsheet di Ingegneria del Software A.A. 2022/2023

## Indice

`

const indiceJSON = fs.readFileSync(percorsoFileIndice, 'utf-8')
const indice = JSON.parse(indiceJSON)

function primaLetteraMaiuscola(stringa) {
    return stringa.charAt(0).toUpperCase() + stringa.slice(1)
}

for (let i = 0; i < indice.capitoli.length; i++) {
    let capitolo = indice.capitoli[i]
    markdown += '- ' + primaLetteraMaiuscola(capitolo) + '\n'
}
markdown += '\n'

for (let i = 0; i < indice.capitoli.length; i++) {
    let capitolo = indice.capitoli[i]
    const markdownCapitolo = fs.readFileSync(capitolo + '.md', 'utf-8')
    markdown += markdownCapitolo + ((i < indice.capitoli.length - 1) ? '\n---\n' : '')
}

const { html, css } = marpit.render(markdown)

const fileHTML = `
<!DOCTYPE html>
<head>
    <style>
        .marpit {
            width: fit-content;
            height: fit-content;
        }
    </style>
</head>
<html style="margin: 0mm; padding: 0mm; height: fit-content; width: fit-content;">
    <body style="margin: 0mm; padding: 0mm; height: fit-content; width: fit-content;">
        <style>${css}</style>
        ${html}
    </body>
</html>
`

puppeteer.launch().then(browser => {
    browser.newPage().then(pagina => {
        pagina.setContent(fileHTML, { waitUntil: 'domcontentloaded' }).then(() => {
            pagina.emulateMediaType('screen').then(() => {
                pagina.pdf({
                    path: percorsoFileOutput,
                    format: 'A4',
                    landscape: true,
                }).then(pdf => {
                    browser.close()
                })
            })
        })
    })
})

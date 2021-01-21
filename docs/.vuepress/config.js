module.exports = {
    title: "LTZone",
    description: "Tony's Blog",
    head: [
        // ...
        ['link', { rel: 'stylesheet', href: "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.5.1/katex.min.css" }],
        ['link', { rel: "stylesheet", href: "https://cdn.jsdelivr.net/github-markdown-css/2.2.1/github-markdown.css" }]
    ],
    markdown: {
        toc: { includeLevel: [1, 2] },
        extendMarkdown: md => {
          md.use(require("markdown-it-katex"))
        }
    }
}
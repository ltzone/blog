module.exports = {
    title: "LTZone",
    description: "Tony's Blog",
    head: [
        // ...
        ['link', { rel: 'stylesheet', href: "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.5.1/katex.min.css" }],
        ['link', { rel: "stylesheet", href: "https://cdn.jsdelivr.net/github-markdown-css/2.2.1/github-markdown.css" }]
    ],
    markdown: {
        extendMarkdown: md => {
          md.use(require("markdown-it-katex"));
          md.use(require('markdown-it-anchor'));
          md.use(require('markdown-it-table-of-contents'), {
        	      includeLevel: [2, 3]
        	    })
        }
    }
}
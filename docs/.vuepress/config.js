const vssueConfig = require('./secret');

module.exports = {
	theme: "reco",
	locales:{
		'/': {
			lang: 'en-US',
			title: 'LTZone',
			description: "Tony's Blog"
		},
		'/zh/': {
			lang: 'zh-CN',
			title: 'LTZone',
			description: "Tony's Blog",
			selectText: '切换语言',
		},
	},
	plugins: {
		"vuepress-plugin-auto-sidebar": {
			titleMode: "titlecase",
			titleMap: {
				"CS222": "CS222 Algorithm Analysis",
				"CS258": "CS258 Information Theory",
				"CS263": "CS263 Programming Language",
				"EI332": "EI332 Computer Composition",
				"EI333": "EI333 Software Engineering",
				"EI338": "EI338 System Engineering",
				"EI339": "EI339 Artificial Intelligence",
				"hol-program": "Lambda Prolog",
				"csapp": "CSAPP Labs",
				"tiger": "OCaml Tiger Compiler"
			},
			unSidebarDir: [
				"/zh/"
			],
		},
		'@vuepress/last-updated': {
		}
	},
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
	},
	themeConfig: {
		type: 'blog',
		authorAvatar: '/id.jpeg',
		subSidebar: 'auto',
		noFoundPageByTencent: false,
		blogConfig:{
			socialLinks: [     // 信息栏展示社交信息
				{ icon: 'reco-mail', link: "mailto:ltzhou@sjtu.edu.cn"},
				{ icon: 'reco-github', link: 'https://github.com/ltzone' },
				{ icon: 'reco-twitter', link: 'https://twitter.com/tonyzhou0608' },
				{ icon: 'reco-zhihu', link: 'https://www.zhihu.com/people/tony-zhou-44-52'}
			]
		},
		author: 'Tony Zhou',
		record: '沪ICP备20004458号',
		recordLink: 'http://www.beian.miit.gov.cn/',
		startYear: '2020',
		locales:{
			'/': {
				nav: [
					{
						text: "Notes",
						items: [
							{ "text": "CS222 Algorithm Analysis", "link": "/course/CS222/" },
							{ "text": "CS258 Information Theory", "link": "/course/CS258/" },
							{ "text": "CS263 Programming Language", "link": "/course/CS263/" },
							{ "text": "EI332 Computer Composition", "link": "/course/EI332/" },
							{ "text": "EI333 Software Engineering", "link": "/course/EI333/" },
							{ "text": "EI338 System Engineering", "link": "/course/EI338/" },
							{ "text": "EI339 Artificial Intelligence", "link": "/course/EI339/" },
						],
						link: "/course/"
					},
					{
						text: "Projects",
						items: [
							{ "text": "OCaml Tiger Compiler", "link": "/projects/tiger/" },
							{ "text": "CSAPP Lab", "link": "/projects/csapp/" },
							{ "text": "LeetCode Record", "link": "/projects/leetcode/" },
							// { "text": "SJTU Go", "link": "/projects/SJTU-Go/" },
							{ "text": "Lambda Prolog", "link": "/projects/hol-program/" },
						],
						link: "/projects/"
					},
					{ text: 'About', link: '/about/'},
					{ text: 'TimeLine', link: '/timeline/', icon: 'reco-date' }
				],
				lastUpdated: 'Last Updated',
			},
			'/zh/': {
				lastUpdated: '最后更新',
				nav: [
					{
						text: "笔记",
						items: [
							{ "text": "CS222 算法设计与分析", "link": "/course/CS222/" },
							{ "text": "CS258 信息论", "link": "/course/CS258/" },
							{ "text": "CS263 程序语言", "link": "/course/CS263/" },
							{ "text": "EI332 计算机组成", "link": "/course/EI332/" },
							{ "text": "EI333 软件工程", "link": "/course/EI333/" },
							{ "text": "EI338 计算机系统工程", "link": "/course/EI338/" },
							{ "text": "EI339 人工智能", "link": "/course/EI339/" },
						],
						link: "/course/"
					},
					{
						text: "项目",
						items: [
							{ "text": "OCaml Tiger Compiler", "link": "/zh/projects/tiger/" },
							{ "text": "CSAPP Lab", "link": "/zh/projects/csapp/" },
							{ "text": "LeetCode刷题记录", "link": "/zh/projects/leetcode/" },
							{ "text": "SJTU Go", "link": "/zh/projects/SJTU-Go/" },
							{ "text": "Lambda Prolog", "link": "/zh/projects/hol-program/" },
						],
						link: "/zh/projects/"
					},
					{ text: '关于我', link: '/zh/about/'},
					{ text: '时间线', link: '/timeline/', icon: 'reco-date' }
				],
			}
		},
		vssueConfig: vssueConfig
	}
}
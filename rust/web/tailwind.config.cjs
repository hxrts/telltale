/** @type {import('tailwindcss').Config} */
module.exports = {
  darkMode: ['class'],
  content: [
    './index.html',
    './src/**/*.{rs,html}',
    '../ui/src/**/*.rs'
  ],
  theme: {
    extend: {
      fontFamily: {
        sans: ['var(--font-sans)'],
        mono: ['var(--font-mono)']
      },
      colors: {
        background: 'oklch(from var(--background) l c h / <alpha-value>)',
        foreground: 'oklch(from var(--foreground) l c h / <alpha-value>)',
        card: 'oklch(from var(--card) l c h / <alpha-value>)',
        border: 'oklch(from var(--border) l c h / <alpha-value>)',
        accent: 'oklch(from var(--accent) l c h / <alpha-value>)',
        muted: 'oklch(from var(--muted) l c h / <alpha-value>)',
        success: 'oklch(from var(--success) l c h / <alpha-value>)',
        warning: 'oklch(from var(--warning) l c h / <alpha-value>)'
      }
    }
  },
  plugins: []
};

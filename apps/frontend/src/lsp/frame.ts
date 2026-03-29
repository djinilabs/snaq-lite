const HEADER = 'Content-Length: '
const SEPARATOR = '\r\n\r\n'

export function encodeFrame(payload: unknown): string {
  const body = JSON.stringify(payload)
  const byteLength = new TextEncoder().encode(body).length
  return `${HEADER}${byteLength}${SEPARATOR}${body}`
}

export function decodeFrames(input: string): { messages: unknown[]; rest: string } {
  const messages: unknown[] = []
  let remaining = input

  while (remaining.startsWith(HEADER)) {
    const sepIndex = remaining.indexOf(SEPARATOR)
    if (sepIndex === -1) {
      break
    }
    const lengthText = remaining.slice(HEADER.length, sepIndex)
    const length = Number(lengthText)
    if (!Number.isFinite(length) || length < 0) {
      break
    }
    const start = sepIndex + SEPARATOR.length
    const end = start + length
    if (remaining.length < end) {
      break
    }
    const body = remaining.slice(start, end)
    messages.push(JSON.parse(body) as unknown)
    remaining = remaining.slice(end)
  }

  return { messages, rest: remaining }
}

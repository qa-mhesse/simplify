import ch.qos.logback.core.ConsoleAppender
import ch.qos.logback.core.FileAppender

appender('FILE', FileAppender) {
    file = 'output.log'
    append = false
    encoder(PatternLayoutEncoder) {
        pattern = "%level %logger - %msg%n"
    }
}

appender('STDOUT', ConsoleAppender) {
    encoder(PatternLayoutEncoder) {
        pattern = "%-5level %-12logger{12} - %msg%n"
    }
}

root(DEBUG, ['FILE', 'STDOUT'])

scan()
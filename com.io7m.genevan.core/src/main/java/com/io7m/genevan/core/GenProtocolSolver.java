/*
 * Copyright © 2022 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */


package com.io7m.genevan.core;

import com.io7m.jaffirm.core.Invariants;
import com.io7m.jaffirm.core.Postconditions;
import com.io7m.jaffirm.core.Preconditions;
import com.io7m.junreachable.UnreachableCodeException;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.genevan.core.GenProtocolErrorCode.AMBIGUOUS_RESULT;
import static com.io7m.genevan.core.GenProtocolErrorCode.CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON;

/**
 * The default protocol solver.
 *
 * @param <C> The type of client handlers
 * @param <S> The type of server endpoints
 */

public final class GenProtocolSolver<
  C extends GenProtocolClientHandlerType,
  S extends GenProtocolServerEndpointType>
  implements GenProtocolSolverType<C, S>
{
  private final GenProtocolStrings strings;

  private GenProtocolSolver(
    final GenProtocolStrings inStrings)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
  }

  /**
   * @param <C> The type of client handlers
   * @param <S> The type of server endpoints
   *
   * @return The default protocol solver using the system's default locale.
   */

  public static <
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  GenProtocolSolverType<C, S> create()
  {
    return create(Locale.getDefault());
  }

  /**
   * @param locale The locale
   * @param <C>    The type of client handlers
   * @param <S>    The type of server endpoints
   *
   * @return The default protocol solver using the given locale.
   */

  public static <
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  GenProtocolSolverType<C, S>
  create(final Locale locale)
  {
    Objects.requireNonNull(locale, "locale");

    try {
      return new GenProtocolSolver<>(new GenProtocolStrings(locale));
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  private static <C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  boolean hasCompatibleServerEndpoint(
    final Set<S> serverEndpoints,
    final C clientHandler)
  {
    return serverEndpoints.stream()
      .anyMatch(s -> s.isCompatibleWith(clientHandler));
  }

  private static <C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  boolean hasCompatibleClientHandler(
    final Set<C> clientHandlers,
    final S serverEndpoint)
  {
    return clientHandlers.stream()
      .anyMatch(s -> s.isCompatibleWith(serverEndpoint));
  }

  private static <C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  Map<String, BestVersionForProtocol<C, S>> collectBestVersions(
    final Map<String, SupportedHandlersForProtocol<C, S>> allProtocols)
  {
    final Map<String, BestVersionForProtocol<C, S>> bestVersions = new HashMap<>();

    for (final var handlers : allProtocols.values()) {
      Preconditions.checkPrecondition(
        !bestVersions.containsKey(handlers.name),
        "Protocol names must be unique"
      );
      bestVersions.put(handlers.name, findBestVersionOf(handlers));
    }

    final var protocolNames =
      allProtocols.keySet()
        .stream()
        .collect(Collectors.toUnmodifiableSet());

    Postconditions.checkPostcondition(
      Objects.equals(bestVersions.keySet(), protocolNames),
      "Best versions must not lose protocol names."
    );
    return bestVersions;
  }

  private static <
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  BestVersionForProtocol<C, S> findBestVersionOf(
    final SupportedHandlersForProtocol<C, S> handlers)
  {
    final var sortedClientHandlers =
      new ArrayList<>(handlers.clientHandlers);
    final var sortedServerEndpoints =
      new ArrayList<>(handlers.serverEndpoints);

    final var clientComparator =
      Comparator.<GenProtocolClientHandlerType, GenProtocolVersion>
          comparing(o -> o.supported().version())
        .reversed();

    final var serverComparator =
      Comparator.<GenProtocolServerEndpointType, GenProtocolVersion>
          comparing(o -> o.supported().version())
        .reversed();

    sortedClientHandlers.sort(clientComparator);
    sortedServerEndpoints.sort(serverComparator);

    for (final var clientHandler : sortedClientHandlers) {
      for (final var serverHandler : sortedServerEndpoints) {
        if (clientHandler.isCompatibleWith(serverHandler)) {
          return new BestVersionForProtocol<>(
            handlers.name,
            serverHandler,
            clientHandler
          );
        }
      }
    }

    /*
     * The preconditions on the SupportedHandlersForProtocol constructor
     * ensure that the above loop _must_ find a result.
     */

    throw new UnreachableCodeException();
  }

  private static <
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  Map<String, SupportedHandlersForProtocol<C, S>> collectSupportedProtocols(
    final Map<String, HandlersForProtocol<C, S>> allProtocols)
  {
    final Map<String, SupportedHandlersForProtocol<C, S>> supported = new HashMap<>();

    for (final var handlers : allProtocols.values()) {
      final var clientHandlers =
        new HashSet<>(handlers.clientHandlers);
      final var serverEndpoints =
        new HashSet<>(handlers.serverEndpoints);

      clientHandlers.removeIf(
        c -> !hasCompatibleServerEndpoint(serverEndpoints, c)
      );
      serverEndpoints.removeIf(
        s -> !hasCompatibleClientHandler(clientHandlers, s)
      );

      if (clientHandlers.isEmpty() || serverEndpoints.isEmpty()) {
        continue;
      }

      supported.put(
        handlers.name,
        new SupportedHandlersForProtocol<C, S>(
          handlers.name, serverEndpoints, clientHandlers)
      );
    }

    return supported;
  }

  private static <C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  Map<String, HandlersForProtocol<C, S>> collectProtocols(
    final Map<String, ServerEndpointsByName<S>> serverEndpointsByName,
    final Map<String, ClientHandlersByName<C>> clientHandlersByName)
  {
    final var collected = new HashMap<String, HandlersForProtocol<C, S>>();

    for (final var serverEndpoints : serverEndpointsByName.values()) {
      final var protocolName = serverEndpoints.name;

      final var clientHandlers =
        clientHandlersByName.getOrDefault(
          protocolName,
          new ClientHandlersByName<>(protocolName, new HashSet<>())
        );

      final var handlers =
        collected.getOrDefault(
          protocolName,
          new HandlersForProtocol<>(
            protocolName,
            new HashSet<>(),
            new HashSet<>())
        );

      handlers.serverEndpoints.addAll(serverEndpoints.serverEndpoints);
      handlers.clientHandlers.addAll(clientHandlers.clientHandlers);
      collected.put(protocolName, handlers);
    }

    for (final var clientHandlers : clientHandlersByName.values()) {
      final var protocolName = clientHandlers.name;

      final var serverEndpoints =
        serverEndpointsByName.getOrDefault(
          protocolName,
          new ServerEndpointsByName<>(protocolName, new HashSet<>())
        );

      final var handlers =
        collected.getOrDefault(
          protocolName,
          new HandlersForProtocol<>(
            protocolName,
            new HashSet<>(),
            new HashSet<>())
        );

      handlers.serverEndpoints.addAll(serverEndpoints.serverEndpoints);
      handlers.clientHandlers.addAll(clientHandlers.clientHandlers);
      collected.put(protocolName, handlers);
    }

    Invariants.checkInvariant(
      collected.keySet().containsAll(clientHandlersByName.keySet()),
      "Protocol set must contain all protocols supported by client handlers."
    );
    Invariants.checkInvariant(
      collected.keySet().containsAll(serverEndpointsByName.keySet()),
      "Protocol set must contain all protocols supported by server endpoints."
    );
    return collected;
  }

  private static <C extends GenProtocolClientHandlerType>
  Map<String, ClientHandlersByName<C>> collectClientHandlers(
    final Collection<? extends C> clientSupports)
  {
    final var collected = new HashMap<String, ClientHandlersByName<C>>();

    for (final var clientHandler : clientSupports) {
      final var supported =
        clientHandler.supported();
      final var identifier =
        supported.identifier();
      final var existing =
        collected.getOrDefault(
          identifier, new ClientHandlersByName<>(identifier, new HashSet<>())
        );

      existing.clientHandlers.add(clientHandler);
      collected.put(identifier, existing);
    }

    final var clientProvidesNames =
      clientSupports.stream()
        .map(e -> e.supported().identifier())
        .collect(Collectors.toUnmodifiableSet());

    Postconditions.checkPostcondition(
      Objects.equals(collected.keySet(), clientProvidesNames),
      "Collected client handlers must not lose protocol names."
    );
    return collected;
  }

  private static <S extends GenProtocolServerEndpointType>
  Map<String, ServerEndpointsByName<S>> collectServerEndpoints(
    final Collection<? extends S> serverProvides)
  {
    final var collected = new HashMap<String, ServerEndpointsByName<S>>();

    for (final var serverEndpoint : serverProvides) {
      final var supported =
        serverEndpoint.supported();
      final var identifier =
        supported.identifier();
      final var existing =
        collected.getOrDefault(
          identifier, new ServerEndpointsByName<>(identifier, new HashSet<>())
        );

      existing.serverEndpoints.add(serverEndpoint);
      collected.put(identifier, existing);
    }

    final var serverProvidesNames =
      serverProvides.stream()
        .map(e -> e.supported().identifier())
        .collect(Collectors.toUnmodifiableSet());

    Postconditions.checkPostcondition(
      Objects.equals(collected.keySet(), serverProvidesNames),
      "Collected server endpoints must not lose protocol names."
    );
    return collected;
  }

  private static <C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>
  Optional<BestVersionForProtocol<C, S>> disambiguate(
    final Map<String, BestVersionForProtocol<C, S>> bestVersions,
    final List<String> preferProtocols)
  {
    for (final var protocol : preferProtocols) {
      final var bestVersion =
        bestVersions.get(protocol);
      if (bestVersion != null) {
        return Optional.of(bestVersion);
      }
    }
    return Optional.empty();
  }

  @Override
  public GenProtocolSolved<C, S> solve(
    final Collection<? extends S> serverProvides,
    final Collection<? extends C> clientSupports,
    final List<String> preferProtocols)
    throws GenProtocolException
  {
    Objects.requireNonNull(serverProvides, "serverProvides");
    Objects.requireNonNull(clientSupports, "clientSupports");
    Objects.requireNonNull(preferProtocols, "preferProtocols");

    if (serverProvides.isEmpty()) {
      throw new GenProtocolException(
        CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
        this.strings.format("errorServerSupportsNothing")
      );
    }

    if (clientSupports.isEmpty()) {
      throw new GenProtocolException(
        CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
        this.strings.format("errorClientSupportsNothing")
      );
    }

    final Map<String, ServerEndpointsByName<S>> serverEndpointsByName =
      collectServerEndpoints(serverProvides);
    final Map<String, ClientHandlersByName<C>> clientHandlersByName =
      collectClientHandlers(clientSupports);

    final Map<String, HandlersForProtocol<C, S>> allProtocols =
      collectProtocols(serverEndpointsByName, clientHandlersByName);
    final Map<String, SupportedHandlersForProtocol<C, S>> supportedProtocols =
      collectSupportedProtocols(allProtocols);

    if (supportedProtocols.isEmpty()) {
      throw this.errorNoProtocolsInCommon(serverProvides, clientSupports);
    }

    final Map<String, BestVersionForProtocol<C, S>> bestVersions =
      collectBestVersions(supportedProtocols);

    if (bestVersions.size() == 1) {
      final var version =
        bestVersions.values()
          .iterator()
          .next();

      return new GenProtocolSolved<>(
        version.clientHandler,
        version.serverEndpoint
      );
    }

    final Optional<BestVersionForProtocol<C, S>> disambiguated =
      disambiguate(bestVersions, preferProtocols);

    if (disambiguated.isPresent()) {
      return new GenProtocolSolved<>(
        disambiguated.get().clientHandler(),
        disambiguated.get().serverEndpoint()
      );
    }

    throw this.errorAmbiguous(
      serverProvides,
      clientSupports,
      preferProtocols
    );
  }

  private GenProtocolException errorNoProtocolsInCommon(
    final Collection<? extends GenProtocolServerEndpointType> serverProvides,
    final Collection<? extends GenProtocolClientHandlerType> clientSupports)
  {
    final var lineSeparator = System.lineSeparator();
    final var text = new StringBuilder(128);
    text.append(this.strings.format("errorNoSupportedVersions"));
    text.append(lineSeparator);
    text.append(lineSeparator);

    text.append(this.strings.format("serverSupports"));
    text.append(lineSeparator);

    for (final var candidate : serverProvides) {
      final var supported = candidate.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    text.append(this.strings.format("clientSupports"));
    text.append(lineSeparator);

    for (final var handler : clientSupports) {
      final var supported = handler.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }

    return new GenProtocolException(
      CLIENT_AND_SERVER_HAVE_NOTHING_IN_COMMON,
      text.toString()
    );
  }

  private GenProtocolException errorAmbiguous(
    final Collection<? extends GenProtocolServerEndpointType> serverProvides,
    final Collection<? extends GenProtocolClientHandlerType> clientSupports,
    final List<String> preferProtocols)
  {
    final var lineSeparator = System.lineSeparator();
    final var text = new StringBuilder(128);
    text.append(this.strings.format("errorAmbiguousProtocols"));
    text.append(lineSeparator);
    text.append(lineSeparator);

    text.append(this.strings.format("serverSupports"));
    text.append(lineSeparator);

    for (final var candidate : serverProvides) {
      final var supported = candidate.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    text.append(this.strings.format("clientSupports"));
    text.append(lineSeparator);

    for (final var handler : clientSupports) {
      final var supported = handler.supported();
      text.append("    ");
      text.append(supported.identifier());
      text.append(" ");
      text.append(supported.version().versionMajor());
      text.append(".");
      text.append(supported.version().versionMinor());
      text.append(lineSeparator);
    }
    text.append(lineSeparator);

    if (!preferProtocols.isEmpty()) {
      text.append(this.strings.format("clientPrefers", preferProtocols));
      text.append(lineSeparator);
    } else {
      text.append(this.strings.format("clientPrefersNone"));
      text.append(lineSeparator);
    }

    text.append(lineSeparator);
    text.append(this.strings.format(
      "clientPreferSuggest",
      serverProvides.stream()
        .map(GenProtocolServerEndpointType::supported)
        .map(GenProtocolIdentifier::identifier)
        .toList()));

    return new GenProtocolException(
      AMBIGUOUS_RESULT,
      text.toString()
    );
  }

  private record ServerEndpointsByName<S extends GenProtocolServerEndpointType>(
    String name,
    Set<S> serverEndpoints)
  {
    private ServerEndpointsByName
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoints, "serverEndpoints");
    }
  }

  private record ClientHandlersByName<C extends GenProtocolClientHandlerType>(
    String name,
    Set<C> clientHandlers)
  {
    private ClientHandlersByName
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(clientHandlers, "clientHandlers");
    }
  }

  private record HandlersForProtocol<
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>(
    String name,
    Set<S> serverEndpoints,
    Set<C> clientHandlers)
  {
    private HandlersForProtocol
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoints, "serverEndpoints");
      Objects.requireNonNull(clientHandlers, "clientHandlers");
    }
  }

  private record SupportedHandlersForProtocol<
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>(
    String name,
    Set<S> serverEndpoints,
    Set<C> clientHandlers)
  {
    private SupportedHandlersForProtocol
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoints, "serverEndpoints");
      Objects.requireNonNull(clientHandlers, "clientHandlers");

      Preconditions.checkPrecondition(
        !serverEndpoints.isEmpty(),
        "Server endpoints cannot be empty"
      );
      Preconditions.checkPrecondition(
        !clientHandlers.isEmpty(),
        "Client handlers cannot be empty"
      );

      for (final var s : serverEndpoints) {
        Preconditions.checkPrecondition(
          hasCompatibleClientHandler(clientHandlers, s),
          "All server endpoints must have a supported client handler."
        );
      }
      for (final var c : clientHandlers) {
        Preconditions.checkPrecondition(
          hasCompatibleServerEndpoint(serverEndpoints, c),
          "All client handlers must have a supported server endpoint."
        );
      }
    }
  }

  private record BestVersionForProtocol<
    C extends GenProtocolClientHandlerType,
    S extends GenProtocolServerEndpointType>(
    String name,
    S serverEndpoint,
    C clientHandler)
  {
    private BestVersionForProtocol
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(serverEndpoint, "serverEndpoint");
      Objects.requireNonNull(clientHandler, "clientHandler");

      Preconditions.checkPrecondition(
        serverEndpoint.isCompatibleWith(clientHandler),
        "Server endpoint must be compatible with client handler."
      );
      Preconditions.checkPrecondition(
        clientHandler.isCompatibleWith(serverEndpoint),
        "Client handler must be compatible with server endpoint."
      );
    }
  }
}
